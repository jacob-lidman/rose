#ifndef FT_HEADER_BEGIN
#define FT_HEADER_BEGIN

#include <iostream>
#include <limits>
#include <map>
#include <vector>
#include <boost/function.hpp>
#include <boost/bimap.hpp>

#include "rose.h"
#include "OmpAttribute.h"

#include "TI.h"
#include "ft_common.h"

/** 
 * @namespace FT
 * @brief Fault-tolerant main namespace, encapsulates FT::Common, FT::Transform, FT::Analysis
 * 
*/

using namespace std;

namespace FT {
   /** 
     * @class FTTransform
     * @brief Fault-tolerant transformations main class. Contains basic transformations for adding redundant computations to
     * a given IR node.
     * The transformations create for inter-/intra- dimension a initialization, execute and unification section. The init. section
     * includes variable declarations and initialization. The execute section performs the redundant computations. Finally, the unifications
     * section unifies the results of the redundant computations by a fault handling policy.
     * @author Jacob Lidman
    */
   class Transform {
     public:
		 //Declarations
		   class SymbDesc;
		   class SymbTerm;
		   class Closure;
		 //Upgrades
		   //... from FT::Common
		     static FT::Common::Region_Desc *upgrade(FT::Transform::Closure *c, FT::Common::Region_Desc *rD);
		 //Misc. functions...
		   static SgBasicBlock *appendStatement(SgStatement *stm, SgBasicBlock *bb, bool neverDelete = false);
		   static string toString(FT::Transform::SymbDesc *desc);
		 //Closure
		   /**
		     * @class Closure
		     * @class Provides a method for data-sharing between policies.
		    */
		   class Closure {
			  public:
			      //Decision functors...
				struct RegionOrder {
				      FT::Transform::Closure *declClos;

				      RegionOrder(FT::Transform::Closure *declClos) {this->declClos = declClos;}
				      //Less-safe
					virtual FT::Common::Region_Desc *lSafe(FT::Common::Region_Desc *x, unsigned int N);
				      //More-safe
					virtual FT::Common::Region_Desc *mSafe(FT::Common::Region_Desc *x, unsigned int N);
				};
			  private:
				//left: original, right: shadow
				boost::bimap<FT::Common::Region_Desc *, FT::Common::Region_Desc *> shadowRegions;
				map<SgName, FT::Transform::SymbTerm *> symDef;
				map<FT::Transform::SymbDesc *, bool> declaredSym;
				FT::Common::Region_Desc rD;
				Closure *pClose;

				Closure::RegionOrder *ROrd;
			  public:
				Closure(Closure *pClose = NULL, RegionOrder *ROrder = NULL) : rD(NULL, SageBuilder::buildVoidType()) {
					this->ROrd = (ROrder == NULL ? new RegionOrder(this) : ROrder);
					this->pClose = pClose;
				}
				~Closure() {}

				//Closure cloning/handling
				  Closure *child();
				  SgBasicBlock *kill();
				//Region handling
				  FT::Common::Region_Desc *lookupOriginal(FT::Common::Region_Desc *regDesc);
				  FT::Common::Region_Desc *lookupShadow(FT::Common::Region_Desc *regDesc);
				  FT::Common::Region_Desc *createShadow(FT::Common::Region_Desc *regDesc);
				  FT::Common::Region_Desc *lessSafe(FT::Common::Region_Desc *x, unsigned int N) {return ROrd->lSafe(x, N);}
				  FT::Common::Region_Desc *moreSafe(FT::Common::Region_Desc *x, unsigned int N) {return ROrd->mSafe(x, N);}
				//Symbol handling
				  FT::Transform::SymbTerm *lookup(SgName n);
				  FT::Transform::SymbDesc *getNamedLoc(SgExpression *loc);
				  bool declareNamedLoc(FT::Transform::SymbDesc *sym);
				  FT::Transform::SymbTerm *addNamedLoc(SgName name, unsigned int N, FT::Common::Region_Desc *r = NULL, SgType *type = NULL);
		    };
		 //Symbol (named location) descriptor
		   class SymbDesc {
			private:
			  Closure *c;
			public:
			//(De)Constructor(s)
			  SymbDesc(Closure *c) {this->c = c;}
			//Functions
			  bool getLHS(set<SgExpression *> &x, unsigned int sI, unsigned int eI);
			  Closure *getClosure() {return c;}
			//Transform symbol interface
			  virtual SgExpression *project(unsigned int N) = 0;
			  virtual FT::Common::SymbDesc::SYM_TYPE getSymType() = 0;
			  virtual unsigned int getN() = 0;
			  virtual void setN(unsigned int N) = 0;
			  virtual SgName getName() = 0;
			  virtual FT::Common::Region_Desc *getRegion() = 0;
		   };
		   class SymbTerm : public FT::Transform::SymbDesc,
				    public FT::Common::SymbTerm {
			protected:
			  virtual void print(ostream &o) const {
				o << "(Transform::SymbTerm-" << this << ") ";
				o << "{<";
					FT::Common::SymbTerm::print(o);
				o << ">}";
			  }
			public:
			//(De)Constructor(s)
			  SymbTerm(Closure *c, FT::Common::SymbTerm *term) :
					FT::Transform::SymbDesc(c), FT::Common::SymbTerm(term->getName(), term->getN(), term->getRegion()) {}
			  SymbTerm(Closure *c, SgName name, unsigned int N, FT::Common::Region_Desc *rD = NULL, SgType *type = NULL) :
					FT::Transform::SymbDesc(c), FT::Common::SymbTerm(name, N, rD, type) {}
			//Functions
			  virtual SgExpression *project(unsigned int N);
			//Transform symbol interface
			  unsigned int getN() {return FT::Common::SymbTerm::getN();}
			  void setN(unsigned int N) {FT::Common::SymbTerm::setN(N);}
			  SgName getName() {return FT::Common::SymbTerm::getName();}
			  FT::Common::SymbDesc::SYM_TYPE getSymType() {return FT::Common::SymbTerm::getSymType();}
			  FT::Common::Region_Desc *getRegion() {return FT::Common::SymbTerm::getRegion();}
		   };
		   class SymbNonTerm : public FT::Transform::SymbDesc,
				     	public FT::Common::SymbNonTerm {
			public:
			//(De)Constructor(s)
			  SymbNonTerm(Closure *c, FT::Common::SymbNonTerm *nonterm) :
					FT::Transform::SymbDesc(c), FT::Common::SymbNonTerm(nonterm->getExp(), nonterm->getRegion()) {}
			  SymbNonTerm(Closure *c, SgExpression *exp, FT::Common::Region_Desc *rD = NULL, SgType *type = NULL) :
					FT::Transform::SymbDesc(c), FT::Common::SymbNonTerm(exp, rD, type) {}
			//Functions
			  virtual SgExpression *project(unsigned int N);
			  void addSymbols(set<FT::Transform::SymbDesc *> &sym) {
				for(set<FT::Transform::SymbDesc *>::iterator it = sym.begin();
				    it != sym.end();
				    ++it) {
					FT::Common::SymbDesc *s = dynamic_cast<FT::Common::SymbDesc *>(*it);
					if(s != NULL)
					   addSymbol(s);
				}
			  }
			//Transform symbol interface
			  unsigned int getN() {return FT::Common::SymbNonTerm::getN();}
			  void setN(unsigned int N) {FT::Common::SymbNonTerm::setN(N);}
			  SgName getName() {return FT::Common::SymbNonTerm::getName();}
			  FT::Common::SymbDesc::SYM_TYPE getSymType() {return FT::Common::SymbNonTerm::getSymType();}
			  FT::Common::Region_Desc *getRegion() {return FT::Common::SymbNonTerm::getRegion();}
		   };
		   

		 //Effect descriptor
		   class Effect {
			public:
				typedef enum {
					EFFECT_EXTENDED_NONE = 0,
					EFFECT_EXTENDED_TRANSFORMED = 1
				} EXTENDED_EFFECT_TYPE;
			private:
				EXTENDED_EFFECT_TYPE eeType;
			public:
				Effect(EXTENDED_EFFECT_TYPE e) {this->eeType = e;}
				EXTENDED_EFFECT_TYPE getExtendedType() {return this->eeType;}

				virtual bool transform(Closure *c, vector<SgStatement *> &stm, FT::Transform::SymbDesc *symDest = NULL) = 0;
		   };
		   class Effect_Transformed : public Effect,
					      public FT::Common::Effect_Extended_Type {
			private:
				vector<SgStatement *> stms;
			protected:

			public:
				Effect_Transformed() : FT::Transform::Effect(EFFECT_EXTENDED_TRANSFORMED), FT::Common::Effect_Extended_Type() {}
				bool transform(Closure *c, vector<SgStatement *> &stm, FT::Transform::SymbDesc *symDest = NULL);

				bool consume(SgStatement *stm);
				bool consume(vector<SgStatement *> &stmList);
		   };
		   struct Effect_Unknown : public Effect, 
					   public FT::Common::Effect_Unknown {
			Effect_Unknown(SgStatement *stm = NULL) : FT::Transform::Effect(EFFECT_EXTENDED_NONE), FT::Common::Effect_Unknown(stm) {}
			bool transform(Closure *c, vector<SgStatement *> &stm, FT::Transform::SymbDesc *symDest = NULL);
		   };
		   struct Effect_Symbolic : public Effect, 
					    public FT::Common::Effect_Symbolic {
			vector<bool> transformedEffects;

			Effect_Symbolic(FT::Common::SymbDesc *exp = NULL) : FT::Transform::Effect(EFFECT_EXTENDED_NONE), FT::Common::Effect_Symbolic(exp) {}
			bool transform(Closure *c, vector<SgStatement *> &stm, FT::Transform::SymbDesc *symDest = NULL);
		   };
		   struct Effect_StaticData : public Effect,
					      public FT::Common::Effect_StaticData {
			Effect_StaticData() : FT::Transform::Effect(EFFECT_EXTENDED_NONE), FT::Common::Effect_StaticData() {}
			bool transform(Closure *c, vector<SgStatement *> &stm, FT::Transform::SymbDesc *symDest = NULL);
		   };
           //Visitors
             /** Named
              * @class FTPragmaVisitor
              * @brief Default implmentation of FTVisitor. Applies fault-tolerance to each statement that has a "#pragma resiliency" proceeding it.
             */
             class FTPragmaVisitor : public Common::FTVisitor {
                    private:
                         bool langHasC, langHasCxx, langHasFortran;
                    public:
                         FTPragmaVisitor() {
                              //Detect language...
                                   langHasC = SageInterface::is_C_language() || SageInterface::is_C99_language();
                                   langHasCxx = SageInterface::is_Cxx_language();
                                   langHasFortran = SageInterface::is_Fortran_language();
                         }
                         bool targetNode(SgNode *node);
             };
		//Control structures...
		  /** 
		    * @class ControlStruct
		    * @brief Abstract class for control-structures
		   */
		   struct ControlStruct {				
		     public:
		     	virtual ~ControlStruct() {}

		          /**
		            * Creates the fault-handling implementation
		            * @param effects A map of the side effects and a descriptor.
		           **/
		          virtual SgStatement *getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList) {
		          	throw FT::Common::FTException("Invalid control structure called.");
		          };
		   };
		   /** 
		    * @class ControlStruct_Check
		    * @brief Abstract class for the control struct. class checks.
		    *	   Structure: sym
		    *			IF(COND(Effect))
		    *				Fault-operation-case
		    *			ELSE
		    *				Proper-operation-case
		   */
		   class ControlStruct_Check : public ControlStruct {
			public:
				struct Comparator {
					SgExpression *getHandler(VariantT compOp, SgType *expType, SgExpression *lhs, SgExpression *rhs);
					bool adjUseAddrOfVar(SgType *t);
				};
				Comparator *c;
			private:
				ControlStruct *faultCase, *properCase;
			public:
				ControlStruct_Check(ControlStruct *faultCase_ = NULL, ControlStruct *properCase_ = NULL, Comparator *c = NULL) {
					this->faultCase = faultCase_;
					this->properCase = properCase_;
					if(c == NULL)
					   this->c = new Comparator();
				}
				virtual pair<SgExpression *, SgStatement *> getCond(Closure *declClos, vector<FT::Common::EffectVal *> &evList);
				SgStatement *getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList);
		   };
		   /** 
		    * @class ControlStruct_Adjudicator
		    * @brief Abstract class for the control struct. class adjudicator.
		    *	   Structure (IF-case is optional): 
		    *			HANDLE(Effect)
		    *			[ IF(Handler-failed)
		    *				Second-level control structure ]
		   */

		   struct ControlStruct_Adjudicator : public ControlStruct {
		          public:
		          	//Adjucator
		            	 /** 
		                   * @class Adjucator
		                   * @brief Abstract class for adjucators
		                   */  
		                   struct Adjucator {
		                      virtual ~Adjucator() {}
		                      virtual SgStatement *getHandler(Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS) = 0;
		                   };
				 /**
				   * @class Adjucator_Meta
				   * @brief Invoke adjucator based on meta condition (AdjucatorDec).
				   */
			       	   struct Adjucator_Meta : public Adjucator {  
				    public:
				      //Meta functor
					struct AdjucatorDec {
					  virtual unsigned long operator()(Closure *declClos, FT::Common::EffectVal *effect);
					};            
				      //Secondary descriptors
				        class AdjucatorMech {
				           private:
					       bool deleteWhenDone;
					       unsigned long condClass;
				               AdjucatorMech *accept, *fail;
				           public:
				               AdjucatorMech(unsigned long condClass, AdjucatorMech *a, AdjucatorMech *f, bool deleteWhenDone = true);
				               virtual ~AdjucatorMech();
				               virtual SgStatement *getHandler(unsigned long cat, Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS);
				        };
				        template <class V> class AdjucatorMech_Term : public AdjucatorMech {
				         private:
					    bool deleteWhenDone;
				            V *adj;
				         public:
				             AdjucatorMech_Term(V *adj = NULL, bool deleteWhenDone = true) : AdjucatorMech(0, this, this, false) {
						if(adj == NULL)
							this->adj = new V();
						else
							this->adj = adj;
						this->deleteWhenDone = deleteWhenDone;
					     }
				             virtual ~AdjucatorMech_Term() {
						if(deleteWhenDone)
							delete adj;
					     }
				             virtual SgStatement *getHandler(unsigned long cat, Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS) {
						if(adj == NULL)
							throw FT::Common::FTException("Adjucator not initialized.");
						else
							return adj->getHandler(declClos, effect, secondCS);
					     }
				        };
				    private:
					 static AdjucatorDec defDecAdj;
					 static AdjucatorMech defMechAdj;

					 AdjucatorDec &decAdj;
				         AdjucatorMech &mechAdj;
				    public:
				         Adjucator_Meta(AdjucatorDec &dAdj = defDecAdj, AdjucatorMech &mAdj = defMechAdj);
				         virtual SgStatement *getHandler(Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS);
				  };
		          private:
			    ControlStruct *secondCS;
		            Adjucator *adj;
		          public:
		            ControlStruct_Adjudicator(Adjucator *adj = NULL, ControlStruct *secondCS = NULL);
			    virtual SgStatement *getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList);
		   };


             //////////////////////////////////////////////////////////////////////////////////////////////////////
             ////////////////////////////////// Non-terminal control structures. //////////////////////////////////
             //////////////////////////////////////////////////////////////////////////////////////////////////////

             //Control structure "Final wish".
               /** 
                * @class ControlStruct_FinalWish
                * @brief Invokes a given statement before (optionally) calling a (N-1)-level handler.
		      *	   Structure: 
		      *			STM
		      *			[ Second-level control structure ]
                */
               struct ControlStruct_FinalWish : public ControlStruct {
                    private:
                         SgStatement *stm;
                         ControlStruct *sLv;
                         bool alwaysExecStm;
                    public:
                         /**
                          * @param stm Statement that is invoked upon fault.
                          * @param secondLevel Optional second level fault handling policy.
                          **/ 
                         ControlStruct_FinalWish(SgStatement *stm, bool alwaysExecStm, ControlStruct *secondLevel) {
                              this->stm = stm;
                              this->sLv = secondLevel;
                              this->alwaysExecStm = alwaysExecStm; 
                         }
                         virtual SgStatement *getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList);
               };

             //Control structure "Second chance".
               /** 
                * @class ControlStruct_SecondChance
                * @brief Perform the computation upto N times while fault occurs, before calling second level handler
		      *	   Structure: 
			 *			for(; ; I++)
			 *				Control-structure "cs"
			 *				IF(Check-control-structure "es")
			 *				   break;
			 *				ELSE	IF(I == N)
			 *					Control-structure "fs"	 
                */
               struct ControlStruct_SecondChance : public ControlStruct {
                    private:
                         int N;
                         ControlStruct *cs, *fs;
					ControlStruct_Check *es;
                    public:
                         /**
                          * @param N The maximum number of times the computations is performed.
                          * @param secondFP Second level fault handling policy.
                          **/ 
                         ControlStruct_SecondChance(ControlStruct *cs, ControlStruct_Check *es, ControlStruct *fs, int N) {
						this->N = N;
						this->cs = cs;
						this->es = es;
						this->fs = fs;
					}
                         virtual SgStatement *getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList);
               };


             //Control structure "Composition".
               /** 
                * @class ControlStruct_Composition
                * @brief Use multiple CS's in sequence
                */
		     struct ControlStruct_Composition : public ControlStruct {
				private:
					vector<ControlStruct *> cs;
				public:
					ControlStruct_Composition(ControlStruct *c0 = NULL, ControlStruct *c1 = NULL, ControlStruct *c2 = NULL,
									    ControlStruct *c3 = NULL, ControlStruct *c4 = NULL, ControlStruct *c5 = NULL,
									    ControlStruct *c6 = NULL, ControlStruct *c7 = NULL, ControlStruct *c8 = NULL) {
						if(c0 != NULL)	   cs.push_back(c0);
						if(c1 != NULL)	   cs.push_back(c1);
						if(c2 != NULL)	   cs.push_back(c2);
						if(c3 != NULL)	   cs.push_back(c3);
						if(c4 != NULL)	   cs.push_back(c4);
						if(c5 != NULL)	   cs.push_back(c5);
						if(c6 != NULL)	   cs.push_back(c6);
						if(c7 != NULL)	   cs.push_back(c7);
						if(c8 != NULL)	   cs.push_back(c8);
					}
					virtual ~ControlStruct_Composition() {}

					virtual SgStatement *getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList);

					void add(ControlStruct *x) {cs.push_back(x);}
					bool remove(ControlStruct *x) {
						for(vector<ControlStruct *>::iterator it = cs.begin(); it != cs.end(); ++it)
						    if(*it == x) {
							  cs.erase(it);
							  return true;
						    }
						return false;
					}
			};

             /////////////////////////////////////////////////////////ymbPath 3, '((array[i - 1] + array[i + 1]) / 2.0)/////////////////////////////////////////////
             ////////////////////////////////////// Terminal fault handlers ///////////////////////////////////////
             //////////////////////////////////////////////////////////////////////////////////////////////////////

             //Control structure "Redundant execute".
               /** 
                * @class ControlStruct_SecondChance
                * @brief Perform the computation upto N times (optionally transforming the effect)
                */
			struct ControlStruct_RedundantExec : public ControlStruct {
				private:
					unsigned int Na;
                         		double Nr;

					struct EffectTransform {
						virtual FT::Common::SymbDesc *transform(unsigned int index, FT::Common::SymbDesc *sym, FT::Common::SymbDesc *effect) {
							return effect;
						}
					} *effTrans;
				public:
                         /**
                          * @param N Redundant executions (absolute)
                          * @param secondFP Second level fault handling policy.
                          **/ 
					ControlStruct_RedundantExec(unsigned int N, EffectTransform *eff = NULL) {
						this->Na = N;
						this->Nr = 0.0;
						this->effTrans = eff;
					}
                         /**
                          * @param N Redundant executions (relative)
                          * @param secondFP Second level fault handling policy.
                          **/ 
					ControlStruct_RedundantExec(double N, EffectTransform *eff = NULL) {
						this->Nr = N;
						this->Na = 0;
						this->effTrans = eff;
					}
					virtual SgStatement *getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList);
			};

             //Adjucator "Mean voting"
               /** 
                * @class Adjucator_Voting
                * @brief returns the mean of the results
                */
               struct Adjucator_Voting_Mean : public ControlStruct_Adjudicator::Adjucator {
                    //Data
		      ControlStruct_Check::Comparator *c;
                      vector<double> weights;
                    //Code
                         Adjucator_Voting_Mean(ControlStruct_Check::Comparator *c_ = NULL) {
						this->c = (c_ == NULL ? new ControlStruct_Check::Comparator() : c_);
					}
                         Adjucator_Voting_Mean(vector<double> w_, ControlStruct_Check::Comparator *c_ = NULL) : weights(w_.begin(), w_.end()) {
						this->c = (c_ == NULL ? new ControlStruct_Check::Comparator() : c_);
					}
                         virtual ~Adjucator_Voting_Mean() {}
                         virtual SgStatement *getHandler(Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS);
               };
             //Adjucator "Median voting"
               /** 
                * @class Adjucator_Voting
                * @brief returns the median of the results
                */
               struct Adjucator_Voting_Median : public ControlStruct_Adjudicator::Adjucator {
			//Data
			  ControlStruct_Check::Comparator *c;
			  SgExpression *medianElement;
			  SgVariableDeclaration *resVec;
			//Code
                          Adjucator_Voting_Median(ControlStruct_Check::Comparator *c_ = NULL) {
				this->c = (c_ == NULL ? new ControlStruct_Check::Comparator() : c_);
				this->medianElement = NULL;					
			  }
                          virtual ~Adjucator_Voting_Median() {}
                          virtual SgStatement *getHandler(Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS);
               };
             //Adjucator "Exact voting" - 
               /** 
                * @class Adjucator_Voting
                * @brief returns the mean of the results
                */
               struct Adjucator_Voting_Exact : public ControlStruct_Adjudicator::Adjucator {
                    //Data
			 ControlStruct_Check::Comparator *c;
                         bool assumeMajElemExist;
                    //Code
                         Adjucator_Voting_Exact(bool assumeMajElemExist = false, ControlStruct_Check::Comparator *c_ = NULL) {
				this->c = (c_ == NULL ? new ControlStruct_Check::Comparator() : c_);
                              	this->assumeMajElemExist = assumeMajElemExist;
                         }
                         virtual ~Adjucator_Voting_Exact() {}
                         virtual SgStatement *getHandler(Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS);
               };

           //Constructor...  
             /**
              * Constructor, initializes class.
              * @param redundancyInter The number of redundant computations in inter-core dimension.
              * @param fPHandlerInter Fault-handling policy for faults in inter-core dimension.
              * @param redundancyIntra The number of redundant computations in intra-core dimension.
              * @param fPHandlerIntra Fault-handling policy for faults in inter-core dimension.
              * @param gScope Default global scope.
              * @param bbExecGlobal Basic block for placing global initialization.
              **/                   
             Transform(SgProject *project = NULL, SgGlobal *gScope = NULL) {
		          this->globalScope = gScope;
		          this->project = project;

		          if(this->project == NULL)
		               this->project = SageInterface::getProject();
		          if(this->globalScope == NULL)
		               this->globalScope = SageInterface::getFirstGlobalScope(this->project);
             }

             ~Transform() {

             }

           //Functions for adding fault tolerance
	     SgNode *transformSingle(vector<FT::Common::EffectVal *> &effects, Closure *closure, ControlStruct &cs, SgGlobal *globalScope = NULL);
             /**
              * Create redundant computations for all underlying nodes, recursivly.
              * @param inputNode AST input node.
              * @param closure Container for all side effects and results, needed in order for multiple statements (in a BB) to share a init. / unification stage.
              * @param globalScope Global scope of inputNode, overrides global scope given to class constructor.
              * @returns NULL if "inputNode" was added to closure or a transformed SgNode (possibly "inputNode" itself)
              **/
             SgNode *transformSingle(SgNode *inputNode, Closure *closure, ControlStruct &cs, SgGlobal *globalScope = NULL);
             /**
              * Create redundant computations for all user specified IR nodes (by visitor).
              * @param startNode Top-most AST input node. If equal to NULL, transformMulti will perform a MemoryPool traversal.
              * @param decisionFunctor Visitor functor. Decides which IR nodes that will be transformed.
              * @param globalScope Global scope of inputNode, overrides global scope given to class constructor.
              **/
             SgNode *transformMulti(ControlStruct &cs, SgNode *startNode = NULL, Common::FTVisitor *decisionFunctor = NULL, SgGlobal *globalScope = NULL);

     private:
           //Instance variables...
             SgProject *project;
             SgGlobal *globalScope;
	   //Helper functions
	     static void revokeEffects(Closure *c, vector<FT::Common::EffectVal *> &effects);
   };
};

#endif
