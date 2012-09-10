#include <iostream>
#include <limits>
#include <map>
#include <vector>
#include <stdexcept>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include <boost/regex.hpp>

#include "rose.h"
#include "TI.h"

#ifdef ROSE_HAS_CUDD
	//CUDD
	#include "util.h"
	#include "cudd.h"
#endif

//The following defines the behavior/assumptions build into the FT modules.
#define FT_TRANFORMATION_NODE_ATTR "FT_TRANSFORMATION_"
#define FT_ASSUME_OPTIMISTIC_ALIASING //Assume two subregions alias unless name tell otherwise, comment to invert
#define FT_POST_ERROR_MSG_AS_SRC_COMMENT
#define FT_POST_WARNING_MSG_ON_SCREEN
#define FT_DEBUG_TRANSFORM 0

using namespace std;

namespace FT {
    /** 
     * @namespace FT::Common
     * @brief Fault-tolerant support namespace. Contains utility functions used by the FTTransform & FTAnalysis classes
     * @author Jacob Lidman
     */
   namespace Common {
		 //CFG definition...

		//Forward declarations
		  class SymbDesc;
		  class SymbTerm;
		  class Region_Desc;
		//Misc functions
		  string toString(SymbDesc *desc);
		 //FT Singleton
		   class Singleton {
    		   	private:
			   //Data members
				#ifdef ROSE_HAS_CUDD
					DdManager *manager;
				#endif
				unsigned int regionCnt;
			   //Unaccessible functions
        			Singleton() {
					srand(time(NULL));
					#ifdef ROSE_HAS_CUDD
						manager = Cudd_Init(0,0,CUDD_UNIQUE_SLOTS,CUDD_CACHE_SLOTS,0);
					#endif

					regionCnt = 0;
				}
				~Singleton() {
					#ifdef ROSE_HAS_CUDD
						Cudd_Quit(manager);
					#endif
				}
        			Singleton(Singleton const&);
       				void operator=(Singleton const&);
		     	public:
        			static Singleton& getInstance() {
            				static Singleton instance;
            				return instance;
        			}
				#ifdef ROSE_HAS_CUDD
					DdManager *getCUDDMan() {return manager;}
				#endif
				unsigned int getRandomInt(unsigned int min, unsigned int max) {return (rand() % max + min);}
				string getRegionName(Region_Desc *r);
		   };
           	//FT Exception
             	  class FTException : public runtime_error {
                    public:
                         FTException(string msg) : runtime_error(msg) {};
             	  };
		//Region descriptor
		  class Region_Desc {
			private:
				Region_Desc *parent;
				map<SgName, Region_Desc *> subRegions;
				SgName regionName;

				SgType *type;
				SymbDesc *sym;
			
				void print(ostream &o) const;
			public:
				Region_Desc(SymbDesc *sym, Region_Desc *parent, SgType *type = NULL, SgName name = "");
				Region_Desc(SymbDesc *sym, SgType *type, SgName name = "");
				~Region_Desc();
				//Generic functions
				  SgName getName() {return regionName;}
				  Region_Desc *getParent() {return parent;}
				  friend ostream &operator<<(ostream &o, const Region_Desc &s) {s.print(o); return o;}
				//Sub-region handling...
				  void getRegionNames(set<SgName> &setRName);
				  unsigned int nrSubRegions() {return subRegions.size();}
				  Region_Desc *getRegion(SgName n);
				  Region_Desc *addRegion(SgName name, Region_Desc *r);
				//Attribute handling
				  bool hasType() {return (this->type != NULL);}
				  SgType *getType() {return this->type;}
				  void setType(SgType *type) {this->type = type;} 
				  bool hasSymbol() {return (sym != NULL);}
				  SymbDesc *getSymbol();
				  void setSymbol(SymbDesc *sym) {this->sym = sym;}
		  };
		 //Symbol descriptor
		   class SymbDesc {
			public:
				typedef enum {
					UNKNOWN = 0,
					TERM = 1,
					NONTERM = 2
				} SYM_TYPE;
			private:
				SYM_TYPE sT;
				SymbTerm *parentSymb;
				Region_Desc *rD;
				set<SymbDesc *> aliasSym;
			protected:
				virtual void print(ostream &o) const;
			public:
				//Functions
				  SymbDesc(SYM_TYPE sT, SgName name, Region_Desc *rD = NULL, SgType *t = NULL);
				  virtual ~SymbDesc() {}
				//Generic functions
				  virtual unsigned int getN() = 0;
				  virtual void setN(unsigned int N) = 0;
				  virtual SgName getName() = 0;
				  SYM_TYPE getSymType() const {return sT;}
				  Region_Desc *getRegion() const {return rD;}
				  void setRegion(Region_Desc *rD) {this->rD = rD;}

				  friend ostream &operator<<(ostream &o, const SymbDesc &s) {s.print(o); return o;}
				//Alias handling...
				  SymbDesc *hasAlias(SgName n);
				  SymbDesc *addAlias(SymbDesc *desc);			  
		   };
		   class SymbTerm : public SymbDesc {
			protected:
				unsigned int N;
				SgName name;

				virtual void print(ostream &o) const;
			public:
				SymbTerm(SgName name, unsigned int N, Region_Desc *rD = NULL, SgType *t = NULL) : SymbDesc(TERM, name, rD, t) {
					this->name = name;
					this->N = N;
				}
				//Generic functions
				  unsigned int getN() {return N;}
			          void setN(unsigned int N) {
					//Make sure N never decreases...
					  if(N > this->N)
					     this->N = N;
				  }
				  SgName getName() {return name;}
		   };
		   class SymbNonTerm : public SymbDesc {
			protected:
				SgExpression *exp;
				set<SymbDesc *> symbols;

				virtual void print(ostream &o) const;
			public:
				SymbNonTerm(SgExpression *exp, Region_Desc *rD = NULL, SgType *t = NULL) : SymbDesc(NONTERM, "", rD, t) {this->exp = exp;}
				//Generic functions
				  SgExpression *getExp() {return exp;}
				  SgName getName();
				  unsigned int getN() {
					if(symbols.size() == 0)
					   return 1;
					//Find minimum N...
					  unsigned int N = std::numeric_limits<unsigned int>::max(), N_;
					  for(set<SymbDesc *>::iterator it = symbols.begin(); it != symbols.end(); ++it) {
					      N_ = (*it)->getN();
					      N = (N < N_ ? N : N_);
					  }
					return N;
				  }
				  void setN(unsigned int N) {
					  for(set<SymbDesc *>::iterator it = symbols.begin(); it != symbols.end(); ++it)
					      (*it)->setN(N);
				  }
				//Symbol handling
				  void addSymbol(SymbDesc *sym) {symbols.insert(sym);}
				  void addSymbols(set<SymbDesc *> &sym) {symbols.insert(sym.begin(), sym.end());}
		   };
		 //Effect descriptor
		   class Effect {
			public:
				typedef enum {
					EFFECT_EXTENDED_TYPE = -1,

					EFFECT_UNKNOWN = 0,
					EFFECT_SYMBOLIC = 1,
					EFFECT_STATICDATA = 2
				} EFFECT_TYPE;
			protected:
				virtual void print(ostream &o) const = 0;
			private:
				unsigned int index;
				EFFECT_TYPE eff;
			public:
				Effect(EFFECT_TYPE effT) {this->eff = effT;}
				virtual ~Effect() {}
				EFFECT_TYPE getType() {return eff;}

				friend ostream &operator<<(ostream &o, const Effect &e) {e.print(o); return o;}
		   };
		   struct Effect_Extended_Type : public Effect {
			protected:
				virtual void print(ostream &o) const = 0;
			public:
				Effect_Extended_Type() : Effect(EFFECT_EXTENDED_TYPE) {}
		   };
		   struct Effect_Unknown : public Effect {
			protected:
				virtual void print(ostream &o) const {
					o << "Effect Unknown {";
					for(vector<SgStatement *>::const_iterator it = stms.begin();
					    it != stms.end();
					    ++it)
						if(*it == NULL)
						   o << "NULL, ";
						else
						   o << (*it)->unparseToString() << ", ";
					o << "}";
				}
			public:
				vector<SgStatement *> stms;

				Effect_Unknown(SgStatement *stm) : Effect(EFFECT_UNKNOWN) {
					if(stm != NULL)
					   stms.push_back(stm);					
				}
		   };
		   struct Effect_Symbolic : public Effect {
			protected:
				virtual void print(ostream &o) const {
					o << "Effect Symbolic {";
					for(vector<SymbDesc *>::const_iterator it = effect.begin();
					    it != effect.end();
					    ++it)
						if(*it == NULL)
						   o << "NULL, ";
						else
							o << *(*it) << ", ";
					o << "}";
				}
			public:
			  	vector<SymbDesc *> effect;

				Effect_Symbolic(SymbDesc *exp = NULL) : Effect(EFFECT_SYMBOLIC) {
					if(exp != NULL)
					   effect.push_back(exp);
				}
		   };
		   struct Effect_StaticData : public Effect {
			protected:
				virtual void print(ostream &o) const {
					o << "Effect Static Data";
				}
			public:
			  	Effect_StaticData() : Effect(EFFECT_STATICDATA) {}
		   };

		 //Types
		   struct EffectVal {
			SymbDesc *s;
			Effect *e;

			EffectVal(SymbDesc *s, Effect *e) {this->s = s; this->e = e;}
			~EffectVal() {delete s; delete e;}

			friend ostream &operator<<(ostream &o, const EffectVal &e) {
				o << "<" << e.s;
				if(e.s != NULL)
				   switch(e.s->getSymType()) {
				    case FT::Common::SymbDesc::UNKNOWN:	o << "-UNKNOWN-" << e.s->getName();	break;
				    case FT::Common::SymbDesc::TERM:	o << "-TERM-" << e.s->getName();	break;
				    case FT::Common::SymbDesc::NONTERM:	o << "-NONTERM-" << e.s->getName();	break;
				   }
				else
					o << "NULL";
				o << ", " << e.e;
				if(e.e != NULL)
				   switch(e.e->getType()) {
				    case FT::Common::Effect::EFFECT_EXTENDED_TYPE:	o << "-EXT. TYPE";	break;
				    case FT::Common::Effect::EFFECT_UNKNOWN:		o << "-UNKNOWN";	break;
				    case FT::Common::Effect::EFFECT_SYMBOLIC:		o << "-SYMBOLIC";	break;
				    case FT::Common::Effect::EFFECT_STATICDATA:		o << "-STATIC DATA";	break;
				   }
				else
					o << "NULL";
				o << ">";
				return o;			
			}
		   };

           //Visitors
             /** 
             * @class FTVisitor
             * @brief Base/abstract class for visitor used by transformMulti function in FTOp class. 
             * Supports memory pool or pre/post order traversal depending on which constructor and traversel function (traverseMemoryPool, traverse) that is used.
             */
             struct FTVisitor : public ROSE_VisitTraversal, public AstPrePostProcessing {
                    private:
                         bool postOrderTraversal;
                         std::vector<SgNode *> targetNodes;
                         std::vector<SgNode *> removeNodes;

                         void visit(SgNode* node);
                         virtual void preOrderVisit(SgNode *node) {
                              if(postOrderTraversal == false)
                                   visit(node);
                         }
                         virtual void postOrderVisit(SgNode *node) {
                              if(postOrderTraversal == true)
                                   visit(node);
                         }
                    protected:
                         void addTarget(SgNode *node);
                         void addRemove(SgNode *node);               
                    public:
                         FTVisitor() {
                              this->postOrderTraversal = true;
                         }
                         FTVisitor(bool postOrder) {
                              this->postOrderTraversal = postOrder;
                         }
                         virtual ~FTVisitor() {}

                         std::vector<SgNode *> &getTargetNodes() {return targetNodes;}
                         std::vector<SgNode *> &getRemoveNodes() {return removeNodes;}

                         virtual bool targetNode(SgNode *node) = 0;
             };
   };
};
