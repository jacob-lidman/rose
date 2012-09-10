#include <iostream>
#include <map>
#include <vector>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>

#include <boost/algorithm/string/replace.hpp>

#include "rose.h"
#include "OmpAttribute.h"

#include "TI.h"
#include "Transform/ft_transform.h"

using namespace std;

///////////////////////////////////////// Misc. functions /////////////////////////////////////////
FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorDec FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::defDecAdj = FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorDec();
FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorMech FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::defMechAdj = 
	FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorMech(1, 
		new FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorMech_Term<FT::Transform::Adjucator_Voting_Exact>(), 
              	new FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorMech(2, 
			new FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorMech_Term<FT::Transform::Adjucator_Voting_Mean>(), 
			new FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorMech_Term<FT::Transform::Adjucator_Voting_Mean>()) );


FT::Common::Region_Desc *FT::Transform::upgrade(FT::Transform::Closure *c, FT::Common::Region_Desc *rD) {
	FT::Common::SymbDesc *comSym = rD->getSymbol();
	ROSE_ASSERT(comSym != NULL);
	//...otherwise be prepared to convert the newly created on...
          FT::Transform::SymbDesc *s = dynamic_cast<FT::Transform::SymbDesc *>(comSym);
          if(s == NULL)
	     switch(comSym->getSymType()) {
		case FT::Common::SymbDesc::TERM: {
			FT::Transform::SymbTerm *t = new FT::Transform::SymbTerm(c, static_cast<FT::Common::SymbTerm *>(comSym));
			rD->setSymbol(static_cast<FT::Common::SymbDesc *>(t));
			s = t;
		    } break;
	        case FT::Common::SymbDesc::NONTERM: {
			FT::Transform::SymbNonTerm *t = new FT::Transform::SymbNonTerm(c, static_cast<FT::Common::SymbNonTerm *>(comSym));
			rD->setSymbol(static_cast<FT::Common::SymbDesc *>(t));
			s = t;
		    } break;
		case FT::Common::SymbDesc::UNKNOWN:
		    ROSE_ASSERT(false);
	     }
	//...if region is a shadow make sure symbol get's declared...
	  if(c->lookupOriginal(rD) != NULL)
	     c->declareNamedLoc(s);

	return rD;
}



SgBasicBlock *FT::Transform::appendStatement(SgStatement *stm, SgBasicBlock *bb, bool neverDelete) {
	SgBasicBlock *bbX = isSgBasicBlock(stm);
	if(bb == NULL) {
	   if(stm == NULL)
		return NULL;
	   if(bbX == NULL)
		return SageBuilder::buildBasicBlock(stm);
	   else
		return bbX;
	} else if(stm == NULL)
	   return bb;

	if(bbX != NULL) {
		for(Rose_STL_Container<SgStatement*>::iterator it = bbX->get_statements().begin();
		    it != bbX->get_statements().end();
		    ++it)
			SageInterface::appendStatement(*it, bb);
		if(!neverDelete)
		   delete stm;
		return bb;
	} else
		SageInterface::appendStatement(stm, bb);
		return bb;
}

string FT::Transform::toString(FT::Transform::SymbDesc *desc) {
	if(desc == NULL)
	   ROSE_ASSERT(false);
	stringstream ss;
	switch(desc->getSymType()) {
	 case FT::Common::SymbDesc::TERM:
		ss << *static_cast<FT::Transform::SymbTerm *>(desc);
		break;
	 case FT::Common::SymbDesc::NONTERM:
		ss << *static_cast<FT::Transform::SymbNonTerm *>(desc);
		break;
	 case FT::Common::SymbDesc::UNKNOWN:
	 default:
		ROSE_ASSERT(false);
	}
	return ss.str();
}

///////////////////////////////////////// Closure /////////////////////////////////////////

//Default region order
FT::Common::Region_Desc *FT::Transform::Closure::RegionOrder::lSafe(FT::Common::Region_Desc *x, unsigned int N) {
	FT::Common::Region_Desc *y, *z;
	//Only use one level of shadows (in default implementation!)
	  if((y = declClos->lookupOriginal(x)) != NULL) 
	      	z = x;
	//Find or create shadow region...
	  else if((z = declClos->lookupShadow(x)) == NULL)
		z = declClos->createShadow(x);
	return z;
}
FT::Common::Region_Desc *FT::Transform::Closure::RegionOrder::mSafe(FT::Common::Region_Desc *x, unsigned int N) {
	FT::Common::Region_Desc *y;
	ROSE_ASSERT((y = declClos->lookupOriginal(x)) != NULL);
	return y;
}

//Closure cloning/handling
FT::Transform::Closure *FT::Transform::Closure::child() {
	return new Closure(this->pClose);
}

SgBasicBlock *FT::Transform::Closure::kill() {
	if(declaredSym.size() == 0)
	   return NULL;

	SgBasicBlock *bbDecl = SageBuilder::buildBasicBlock();
	for(map<FT::Transform::SymbDesc *, bool>::iterator it = declaredSym.begin(); it != declaredSym.end(); ++it) {
		//Create terminals that were declared within current closure...
		  if(!it->second)
		     continue;
		  FT::Transform::SymbDesc *symDesc = it->first;
		//Create variable...
		  SgType *type = symDesc->getRegion()->getType();
		  if(symDesc->getN() > 1)
		  	type = SageBuilder::buildArrayType(type, SageBuilder::buildIntVal(symDesc->getN()));
		  SageInterface::appendStatement(SageBuilder::buildVariableDeclaration(symDesc->getName(), type, NULL, bbDecl), bbDecl);
	}

	delete this;


	#if FT_DEBUG_TRANSFORM > 3
		cout << "Closure output (" << bbDecl << "): {" << endl;
		#if FT_DEBUG_TRANSFORM > 4
			for(SgStatementPtrList::iterator it = bbDecl->get_statements().begin();
			    it != bbDecl->get_statements().end();
			    ++it)
				cout << (*it)->unparseToString() << endl;
		#endif
		cout << "}" << endl;
	#endif


	return bbDecl;
}
//Region handling
FT::Common::Region_Desc *FT::Transform::Closure::lookupOriginal(FT::Common::Region_Desc *shadowReg) {
	boost::bimap<FT::Common::Region_Desc *, FT::Common::Region_Desc *>::right_iterator it = shadowRegions.right.find(shadowReg);
	if(it != shadowRegions.right.end())
	   return it->second;
	else
		return NULL;
}
FT::Common::Region_Desc *FT::Transform::Closure::lookupShadow(FT::Common::Region_Desc *origReg) {
	boost::bimap<FT::Common::Region_Desc *, FT::Common::Region_Desc *>::left_iterator it = shadowRegions.left.find(origReg);
	if(it != shadowRegions.left.end())
	   return it->second;
	else
		return NULL;
}
FT::Common::Region_Desc *FT::Transform::Closure::createShadow(FT::Common::Region_Desc *regDesc) {
	//Make sure a shadow hasn't already been assigned...
	  ROSE_ASSERT(lookupShadow(regDesc) == NULL);
	//Create shadow name...
	  SgName shadowName = regDesc->getName();
	  boost::replace_all(shadowName.getString(), " ", "");
	  shadowName += "_FT";
	//Create shadow region...
	  FT::Common::Region_Desc *regShadow = new FT::Common::Region_Desc(NULL, regDesc->getType(), shadowName);
	  #if FT_DEBUG_TRANSFORM > 0
	  	cout << "Added shadow '" << *regShadow << "'." << endl;
	  #endif
	//Store in map...
	  shadowRegions.insert( boost::bimap<FT::Common::Region_Desc *, FT::Common::Region_Desc *>::value_type(regDesc, regShadow) );

	return regShadow;
}

//Symbol handling
FT::Transform::SymbTerm *FT::Transform::Closure::lookup(SgName n) {
	//Try to locate symbol...
	  map<SgName, FT::Transform::SymbTerm *>::iterator it = symDef.find(n);
	  if(it == symDef.end()) {
		if(this->pClose != NULL) {
		   FT::Transform::SymbTerm *s = this->pClose->lookup(n);
		   if(s != NULL)
			return s;
		}
		return NULL;
	  }
	//Locate shadow (if any)...
	  FT::Common::Region_Desc *shadowReg = NULL, *x = it->second->getRegion();
	  while(x != NULL) {
		shadowReg = x;
		x = lookupShadow(x);
	  }
	  if(shadowReg != it->second->getRegion()) {
		FT::Transform::SymbTerm *s = dynamic_cast<FT::Transform::SymbTerm *>(shadowReg->getSymbol());
		ROSE_ASSERT(s != NULL);
		return s;
	  } else
		return it->second;
}
	  
FT::Transform::SymbDesc *FT::Transform::Closure::getNamedLoc(SgExpression *loc) {
	//Check if exp already has been transformed...
	  if(TInterface::hasValueAttribute(loc, FT_TRANFORMATION_NODE_ATTR "VAR")) {
		FT::Common::Region_Desc *rD = TInterface::GetValueAttribute<FT::Common::Region_Desc *>(loc, FT_TRANFORMATION_NODE_ATTR "VAR");
		return dynamic_cast<FT::Transform::SymbDesc *>(rD->getSymbol());
	  }
	//Define and execute transformation...
	  set<FT::Transform::SymbDesc *> top;
	  struct Visitor {
		set<FT::Transform::SymbDesc *> *symbols;
		Closure *c;
		Visitor(Closure *c, set<FT::Transform::SymbDesc *> *s) {
			this->c = c; 
			this->symbols = s;
		}
		virtual FT::Common::Region_Desc *visit(SgExpression *exp, bool needRegion) {
			//Make sure exp hasn't already been assigned a name...
			  if(TInterface::hasValueAttribute(exp, FT_TRANFORMATION_NODE_ATTR "VAR"))
			     return TInterface::GetValueAttribute<FT::Common::Region_Desc *>(exp, FT_TRANFORMATION_NODE_ATTR "VAR");
			//Specific handlers
			  switch(exp->variantT()) {
			   case V_SgDotExp:
			   case V_SgArrowExp:
			   case V_SgPntrArrRefExp: {
			      //Take care of LHS & RHS...
				FT::Common::Region_Desc *rDBase = visit(static_cast<SgBinaryOp *>(exp)->get_lhs_operand(), true),
			      				*rDOff = visit(static_cast<SgBinaryOp *>(exp)->get_rhs_operand(), true);
			      //Create a new region for use as subregion...
				FT::Common::Region_Desc *rDSubReg = 
					new FT::Common::Region_Desc(NULL, rDBase, exp->get_type(), rDBase->getName() + "_" + rDOff->getName());
				rDBase->addRegion(rDSubReg->getName(), rDSubReg);
			      return rDSubReg; }
			   case V_SgVarRefExp: {
				SgName name = static_cast<SgVarRefExp *>(exp)->get_symbol()->get_name();
				FT::Transform::SymbDesc *sD = c->lookup(name);
				if(sD == NULL)
				   sD = c->addNamedLoc(name, 1, NULL, exp->get_type());
				//Tag expression...
				  ROSE_ASSERT(sD->getRegion() != NULL);
				  TInterface::AddValueAttribute<FT::Common::Region_Desc *>(exp, FT_TRANFORMATION_NODE_ATTR "VAR", sD->getRegion());
				//Add symbol
				  symbols->insert(sD);
				return sD->getRegion();
			    } break;
			   default:
				break;
			  }
			SgBinaryOp *bOp;
			if((bOp = isSgBinaryOp(exp)) != NULL) {
			   //Do we need to supply caller with a region?
			     if(needRegion) {
				//Swap symbol set...
				  set<FT::Transform::SymbDesc *> *sTemp = symbols, sSwapLHS, sSwapRHS;
				//Visit LHS & RHS...
				  symbols = &sSwapRHS;
			   	  visit(bOp->get_rhs_operand(), false);
				  symbols = &sSwapLHS;
			   	  visit(bOp->get_lhs_operand(), false);
				//Create symbol...
				  FT::Transform::SymbNonTerm *p = new FT::Transform::SymbNonTerm(this->c, exp, NULL, bOp->get_type());
				  p->addSymbols(sSwapLHS);
				  p->addSymbols(sSwapRHS);
				//Finalize and return region...
				  symbols = sTemp;
				return p->getRegion();
			     } else {
			   	visit(bOp->get_rhs_operand(), false);
			   	visit(bOp->get_lhs_operand(), false);
			   	return NULL;
			     }
			}
			SgUnaryOp *uOp;
			if((uOp = isSgUnaryOp(exp)) != NULL) {
			   //Do we need to supple caller with a region?
			     if(needRegion) {
				//Copy and swap symbol set...
				  set<FT::Transform::SymbDesc *> *sTemp = symbols, sSwap;
				  symbols = &sSwap;
				//Visit LHS & RHS...
			   	  visit(uOp->get_operand_i(), false);
				//Create symbol...
				  FT::Transform::SymbNonTerm *p = new FT::Transform::SymbNonTerm(this->c, exp, NULL, uOp->get_type());
				  p->addSymbols(sSwap);
				//Finalize and return region...
				  symbols = sTemp;
				return p->getRegion();
			     } else {
			  	visit(uOp->get_operand_i(), false);
			  	return NULL;
			     }
			}

			if(needRegion) {
				SgValueExp *val;
				if((val = isSgValueExp(exp)) != NULL) {
					//Create terminal symbol...
					  stringstream ss;
					  switch(val->variantT()) {
					   case V_SgEnumVal:		ss << static_cast<SgEnumVal *>(exp)->get_value();			break;
					   case V_SgIntVal:		ss << static_cast<SgIntVal *>(exp)->get_value();			break;
					   case V_SgLongIntVal:		ss << static_cast<SgLongIntVal *>(exp)->get_value();			break;
					   case V_SgLongLongIntVal:	ss << static_cast<SgLongLongIntVal *>(exp)->get_value();		break;
					   case V_SgShortVal:		ss << static_cast<SgShortVal *>(exp)->get_value();			break;
					   case V_SgUnsignedIntVal:	ss << static_cast<SgUnsignedIntVal *>(exp)->get_value();		break;
					   case V_SgUnsignedShortVal: 	ss << static_cast<SgUnsignedShortVal *>(exp)->get_value();		break;
					   default:
						cout << "Unhandled value in getNamedLoc()::Visitor::visit(): '" << exp->class_name() << "' (" << exp << ")." << endl;
						ROSE_ASSERT(false);
					  }
					  FT::Transform::SymbTerm *p = new FT::Transform::SymbTerm(this->c, ss.str(), 1, NULL, val->get_type());
					//Return region...
					  return p->getRegion();
				}
				cout << "Unhandled case in getNamedLoc()::Visitor::visit(): '" << exp->class_name() << "' (" << exp << ")." << endl;
				ROSE_ASSERT(false);
			} else
				return NULL;
		}
	  } traverser(this, &top);
	  FT::Common::Region_Desc *rD = traverser.visit(loc, false);
	  if(rD == NULL) {
		FT::Transform::SymbNonTerm *p = new FT::Transform::SymbNonTerm(this, loc, NULL, loc->get_type());
		p->addSymbols(top);
		return p;
	  } else {
		//Make sure region has a symbol...
		  if(rD->hasSymbol())
		     //Upgrade it...
		       rD = upgrade(this, rD);
		  else {
			//Create path symbol...
			  FT::Transform::SymbNonTerm *p = new FT::Transform::SymbNonTerm(this, loc, rD, NULL);
			  p->addSymbols(top);
			//Set symbol...
			  rD->setSymbol(p);
		  }
		return dynamic_cast<FT::Transform::SymbDesc *>(rD->getSymbol());
	  }
}

FT::Transform::SymbTerm *FT::Transform::Closure::addNamedLoc(SgName name, unsigned int N, FT::Common::Region_Desc *r, SgType *type) {
	FT::Transform::SymbTerm *symTerm;
	//Has variable already been declared...
	  if((symTerm = lookup(name)) != NULL)
	     return symTerm;
	//Create variable...
	  symTerm = new FT::Transform::SymbTerm(this, name, N, r, type);
	  symDef[name] = symTerm;

	return symTerm;
}

bool FT::Transform::Closure::declareNamedLoc(FT::Transform::SymbDesc *sym) {
	declaredSym[sym] = true;

	return true;
}

///////////////////////////////////////// Symbol /////////////////////////////////////////

bool FT::Transform::SymbDesc::getLHS(set<SgExpression *> &x, unsigned int sI, unsigned int eI) {
	for(unsigned int i = sI; i < eI; i++)
	    x.insert( project(i) );
	return true;
}

SgExpression *FT::Transform::SymbTerm::project(unsigned int N) {
	//Create expression...
	unsigned int N_ = N % getN();
	if(getClosure()->lookupOriginal(getRegion()) == NULL) //...is original...
	   return SageBuilder::buildVarRefExp(name);
	else
	   return SageBuilder::buildPntrArrRefExp(
			SageBuilder::buildVarRefExp(name),
			SageBuilder::buildIntVal(N_));
}

SgExpression *FT::Transform::SymbNonTerm::project(unsigned int N) {
	//Define and execute attribute localization...
	  struct Visitor : public AstSimpleProcessing {
		SgExpression *topExp;
		vector<pair<SgExpression *, SgExpression *> > replaceVec;
		unsigned int i;
		Visitor(unsigned int i_) : i(i_) {this->i = i_; this->topExp = NULL;}
		virtual void visit(SgNode *n) {
			SgExpression *exp = isSgExpression(n);
			if(exp == NULL)	
				return;
			//Make sure we haven't visited parent already...
			  for(vector<pair<SgExpression *, SgExpression *> >::iterator it = replaceVec.begin();
			      it != replaceVec.end();
			      ++it) {
				if( TInterface::isParentOf(exp, (*it).first) )
				    return;
				ROSE_ASSERT( !TInterface::isParentOf((*it).first, exp) ); //this shouldn't happen with preorder traversal.
			  }
			  if(topExp == NULL) 
			     topExp = exp;
			//Tag expression
			  if(!TInterface::hasValueAttribute(n, FT_TRANFORMATION_NODE_ATTR "VAR"))
			     return;
			  FT::Common::Region_Desc *rD = TInterface::GetValueAttribute<FT::Common::Region_Desc *>(n, FT_TRANFORMATION_NODE_ATTR "VAR");
			  ROSE_ASSERT(rD != NULL);
			  FT::Transform::SymbDesc *sD = dynamic_cast<FT::Transform::SymbDesc *>(rD->getSymbol());
			  ROSE_ASSERT(sD != NULL);

			  SgExpression *p = sD->project(i);
			  replaceVec.push_back( pair<SgExpression *, SgExpression *>(exp, p) );
		}
		void atTraversalEnd() {
			//Replace expressions (children first)...
			  for(vector<pair<SgExpression *, SgExpression *> >::iterator it = replaceVec.begin();
			      it != replaceVec.end();
			      ++it)
 				if( (*it).first == topExp )
				    topExp = (*it).second;
				else
				    SageInterface::replaceExpression( (*it).first, (*it).second );
		}	
	  } expTransformer(N);
	  SgExpression *exp = SageInterface::copyExpression(this->exp);  
	  expTransformer.traverse(exp, preorder);
	return expTransformer.topExp;
}

///////////////////////////////////////// Effects /////////////////////////////////////////
bool FT::Transform::Effect_Transformed::consume(vector<SgStatement *> &stmList) {
      //Insert stmt...
	for(vector<SgStatement *>::iterator it = stmList.begin(); it != stmList.end(); ++it)
	    if(!consume(*it))
	       return false;

      return true;
}
bool FT::Transform::Effect_Transformed::consume(SgStatement *stm) {
      //Insert stmt...
	stms.push_back(stm);

      return true;
}

bool FT::Transform::Effect_Transformed::transform(Closure *c, vector<SgStatement *> &stm, FT::Transform::SymbDesc *symDest) {
	stm.insert(stm.end(), stms.begin(), stms.end());
	return true;
}

bool FT::Transform::Effect_Unknown::transform(Closure *c, vector<SgStatement *> &stm, FT::Transform::SymbDesc *symDest) {
	ROSE_ASSERT(symDest == NULL);
	stm.insert(stm.end(), this->stms.begin(), this->stms.end());
	return true;
}

bool FT::Transform::Effect_Symbolic::transform(Closure *c, vector<SgStatement *> &stm, FT::Transform::SymbDesc *symDest) {
	//Enlarge (if neccessary) vector that describes wheather effect has been committed
	  if(transformedEffects.size() < this->effect.size())
	     transformedEffects.resize(this->effect.size(), false);
	//Transform effects...
	  for(unsigned int i = 0; i < this->effect.size(); i++) {
	      FT::Transform::SymbDesc *symEffect = dynamic_cast<FT::Transform::SymbDesc *>(this->effect[i]);
	      if(symEffect == NULL)
	         return false;
	      //Has effect already been transformed (relative update)?
	        if(transformedEffects[i])
	           continue;
	        else
		    transformedEffects[i] = true;
	      //Is effect destionation specified?
	        if(symDest == NULL)
	           stm.push_back(SageBuilder::buildExprStatement(symEffect->project(i)) );
	        else
		   stm.push_back(SageBuilder::buildAssignStatement(symDest->project(i), symEffect->project(i)) );
	  }
	return true;
}

bool FT::Transform::Effect_StaticData::transform(Closure *c, vector<SgStatement *> &stm, FT::Transform::SymbDesc *symDest) {
	if(symDest != NULL) {
	   stm.push_back( SageBuilder::buildVariableDeclaration(symDest->getName(), symDest->getRegion()->getType()) );
	   return true;
	} else
		return false;
}

///////////////////////////////////////// Visitors /////////////////////////////////////////
void FT::Common::FTVisitor::visit(SgNode* node) {
     //Make sure node is OK
       ROSE_ASSERT(node != NULL);
     //Should node be enhanced...
       if(targetNode(node) == true)
          targetNodes.push_back(node);
}

void FT::Common::FTVisitor::addTarget(SgNode *node) {
     //Make sure a child of node hasn't been added
       std::vector<int> childNodes;
       int index = 0;
       for(std::vector<SgNode *>::iterator it = targetNodes.begin();
           it != targetNodes.end();
           ++it)
               if(TInterface::isParentOf(*it, node)) {
                    SgLocatedNode *ln;
                    if((ln = isSgLocatedNode(*it)) != NULL)
                         cout << ln->get_file_info()->get_filenameString() << ":" << ln->get_file_info()->get_line();
                    else
                         cout << "???:?";
                    cout << ") Ignoring node '" << (*it)->class_name() << "' (" << *it << ") as parent node '" 
                         << node->class_name() << "' (" << node << ") is scheduled for transformation." << endl;
                    childNodes.push_back(index);
               } else
                    index++;
     //Make sure node is not the child of another node
       for(std::vector<SgNode *>::iterator it = targetNodes.begin();
           it != targetNodes.end();
           ++it)
               if(TInterface::isParentOf(node, *it)) {
                    SgLocatedNode *ln;
                    if((ln = isSgLocatedNode(*it)) != NULL)
                         cout << ln->get_file_info()->get_filenameString() << ":" << ln->get_file_info()->get_line();
                    else
                         cout << "???:?";
                    cout << ") Ignoring node '" << node->class_name() << "' (" << node << ") as parent node '" 
                         << (*it)->class_name() << "' (" << *it << ") is scheduled for transformation." << endl;
                    return;
               }
     //Remove childs if any...
       for(std::vector<int>::iterator it = childNodes.begin();
           it != childNodes.end();
           ++it)
               targetNodes.erase( targetNodes.begin() + *it );
     //Add node
       targetNodes.push_back(node);
}
void FT::Common::FTVisitor::addRemove(SgNode *node) {
     //Make sure a child of node hasn't been added
       std::vector<int> childNodes;
       int index = 0;
       for(std::vector<SgNode *>::iterator it = removeNodes.begin();
           it != removeNodes.end();
           ++it)
               if(TInterface::isParentOf(*it, node))
                    childNodes.push_back(index);
               else
                    index++;
     //Make sure node is not the child of another node
       for(std::vector<SgNode *>::iterator it = removeNodes.begin();
           it != removeNodes.end();
           ++it)
               if(TInterface::isParentOf(node, *it))
                    return;
     //Remove childs if any...
       for(std::vector<int>::iterator it = childNodes.begin();
           it != childNodes.end();
           ++it)
               removeNodes.erase( removeNodes.begin() + *it );
     //Add node
       removeNodes.push_back(node);
} 

bool FT::Transform::FTPragmaVisitor::targetNode(SgNode *node) {
     //Handle differently depending on language...
     if(langHasC || langHasCxx) {
          //Is this our pragma?
            if(node->variantT() == V_SgPragmaDeclaration) {
               boost::regex commentMatcher(string("[[:space:]]*resiliency.*"), boost::regex::icase);
               SgPragmaDeclaration *pragmaDecl = isSgPragmaDeclaration(node);
               SgPragma *pragma = pragmaDecl->get_pragma();
               //Make sure the pragma is correct..
                 if(!boost::regex_match(pragma->get_pragma().c_str(), commentMatcher, boost::match_extra))
                    return false;              
               //Make sure there is a next statement...
                 SgStatement *stm = SageInterface::getNextStatement(pragmaDecl);
                 if(stm == NULL)
                    return false;
               //Print debug message if appropriate...
                 if(SgProject::get_verbose()>0)
                   cout << "Pragma: '" << pragma->get_pragma() << "' -> " << stm->class_name() << endl;
               //Remove pragma declaration from AST
                 addRemove(pragmaDecl);
               //Add node for transformation...
                 addTarget(stm);
            } 
     } 

     if(langHasFortran) {
          //Try to get comment
            SgStatement *stm;
            if((stm = isSgStatement(node)) == NULL)
               return false;
          //Extract PreProcInfoFT::Common::SymbDesc *
            Rose_STL_Container< PreprocessingInfo* > *preproc = stm->getAttachedPreprocessingInfo();
            if(preproc == NULL)
               return false;
            boost::regex commentMatcherF90("[[:space:]]*!\\$[[:space:]]*resiliency.*", boost::regex::icase),
                         commentMatcherF("C\\$[[:space:]]*resiliency.*", boost::regex::icase);
            for(Rose_STL_Container< PreprocessingInfo* >::iterator it = preproc->begin();
                it != preproc->end();
                ++it)
                    //cout << "Comment: '" << (*it)->getString() << "'" << endl;
                    if( ((*it)->getTypeOfDirective() == PreprocessingInfo::FortranStyleComment) ||
                        ((*it)->getTypeOfDirective() == PreprocessingInfo::F90StyleComment) )
                         if(boost::regex_match((*it)->getString().c_str(), commentMatcherF90) ||
                            boost::regex_match((*it)->getString().c_str(), commentMatcherF)) {
                              SgStatement *nstm = SageInterface::getNextStatement(stm);
                              //Print debug message if appropriate...
                                if(SgProject::get_verbose()>0)
                                   cout << "Pragma: '" << (*it)->getString().substr(2) << "' -> " << nstm->class_name() << endl;
                              //Add node for transformation...
                                   addTarget(nstm);
                         }
     }

     return false;
}

///////////////////////////////////////////////////////////////////////////////////////////////////////

SgNode *FT::Transform::transformSingle(vector<FT::Common::EffectVal *> &effects, Closure *closure, ControlStruct &cs, SgGlobal *globalScope) {
	//Try given controlstruct...
	  SgStatement *s = cs.getHandler(closure, effects);
	  if(effects.size() == 0)
	     return s;
	//Handle the remaining effects
	  SgBasicBlock *bb = SageBuilder::buildBasicBlock();
	  vector<FT::Common::EffectVal *> remEffects;
	  for(vector<FT::Common::EffectVal *>::iterator it = effects.begin(); it != effects.end(); ++it) {
		SymbDesc *symbTransform = dynamic_cast<SymbDesc *>( (*it)->s );
	        switch((*it)->e->getType()) {
	         case FT::Common::Effect::EFFECT_EXTENDED_TYPE: 
			break;
	         case FT::Common::Effect::EFFECT_UNKNOWN: {
			//TODO! Write data from shadows -> originals

			//Apply transformation...
		     	  vector<SgStatement *> stms;
		     	  ROSE_ASSERT( static_cast<Effect_Unknown *>( (*it)->e )->transform(closure, stms, symbTransform) );
		     	  SageInterface::appendStatementList(stms, bb);
		   	//Make sure effect is removed...
		     	  remEffects.push_back(*it);
		  } break;
	         case FT::Common::Effect::EFFECT_SYMBOLIC:
			//This should have been handled...
			  ROSE_ASSERT(false);	
	         case FT::Common::Effect::EFFECT_STATICDATA:
			//Add this effect as a named location that needs to be declarared...
			  ROSE_ASSERT(closure->declareNamedLoc(symbTransform));
			break;
	        }
	  }
	//Revoke effects...
	  revokeEffects(closure, remEffects);
	//Return the results...
	  return bb;
}

SgNode *FT::Transform::transformSingle(SgNode *inputNode, Closure *c, ControlStruct &cs, SgGlobal *globalScope) {
     //Initialization   
       SgNode *nodePtrA, *nodePtrB, *nodePtrC, *nodePtrD;
       SgStatementPtrList *stmBodyList;
       SgStatement *stmBody;
       SgVariableDeclaration *varDecl;
       if((inputNode == NULL) || (c == NULL))
	  return NULL;

     //Mark node as having been transformed...
       ROSE_ASSERT(TInterface::hasValueAttribute(inputNode, FT_TRANFORMATION_NODE_ATTR "VISITED") == false);
       inputNode->addNewAttribute(FT_TRANFORMATION_NODE_ATTR "VISITED", new AstTextAttribute("TRUE"));

     //Recursivly handle statement(s)
       if(TInterface::IsLoop(inputNode, &nodePtrA, &nodePtrB, &nodePtrC, &nodePtrD)) {
	  #if FT_DEBUG_TRANSFORM > 0
	      cout << "[Transform-Loop] ";
	      #if FT_DEBUG_TRANSFORM > 4
	      	  cout << inputNode->unparseToString();
       	      #endif
	      cout << endl;
       	  #endif
	  Closure *cC = c->child();
	  SgStatement *node = isSgStatement(transformSingle(nodePtrD, cC, cs, globalScope));
	  SgBasicBlock *bb = (node == NULL ? appendStatement(isSgStatement(nodePtrD), cC->kill()) : appendStatement(node, cC->kill()));
	  #if FT_DEBUG_TRANSFORM > 3
		cout << "Output Loop: ";
		if(bb != NULL)
			cout << "BB (" << bb << ")" << endl;
		else
			cout << "NULL" << endl;
	  #endif
          TInterface::SetLoop(inputNode, nodePtrA, nodePtrB, nodePtrC, bb);
          return inputNode;
       } else if(TInterface::IsIf(inputNode, &nodePtrA, &nodePtrB, &nodePtrC)) {
	  #if FT_DEBUG_TRANSFORM > 0
	      cout << "[Transform-If] ";
	      #if FT_DEBUG_TRANSFORM > 4
	      	  cout << inputNode->unparseToString();
       	      #endif
	      cout << endl;
       	  #endif
	  Closure *cCA = c->child(), *cCB = c->child();
	  SgStatement *nodeA = isSgStatement(transformSingle(nodePtrB, cCA, cs, globalScope)),
		      *nodeB = isSgStatement(transformSingle(nodePtrC, cCB, cs, globalScope));
	  if(nodePtrB != NULL)
	     nodeA = (nodeA == NULL ? appendStatement(isSgStatement(nodePtrB), cCA->kill()) : appendStatement(nodeA, cCA->kill()));
	  if(nodePtrC != NULL)
	     nodeB = (nodeA == NULL ? appendStatement(isSgStatement(nodePtrC), cCB->kill()) : appendStatement(nodeB, cCB->kill()));	     
          TInterface::SetIf(inputNode, nodePtrA, nodeA, nodeB);
	  #if FT_DEBUG_TRANSFORM > 3
	  	cout << "Output If: ";
		if(nodeA != NULL)
		   cout << nodeA->class_name() << " (" << nodeA << ") ";
		else
		   cout << "NULL ";
		if(nodeB != NULL)
		   cout << nodeB->class_name() << " (" << nodeB << ") " << endl;
		else
		   cout << "NULL " << endl;		
	  #endif
          return inputNode;
       } else if((varDecl = isSgVariableDeclaration(inputNode)) != NULL) {
	  #if FT_DEBUG_TRANSFORM > 0
	      cout << "[Transform-VariableDecl.] ";
	      #if FT_DEBUG_TRANSFORM > 4
	      	  cout << inputNode->unparseToString();
       	      #endif
	      cout << endl;
       	  #endif
	  vector<FT::Common::EffectVal *> effects;
	  for(SgInitializedNamePtrList::iterator it = varDecl->get_variables().begin(); it != varDecl->get_variables().end(); ++it) {
		//Add static effect...
		  FT::Transform::SymbTerm *symb = dynamic_cast<FT::Transform::SymbTerm *>( c->addNamedLoc((*it)->get_name(), 1, NULL, (*it)->get_typeptr()) );
		  ROSE_ASSERT(symb != NULL);
	          #if FT_DEBUG_TRANSFORM > 2
	      	      cout << "(VarDecl) Added effect (" << FT::Common::toString(symb) << ", STATIC-DATA)" << endl;
       	          #endif
	      	  effects.push_back( new FT::Common::EffectVal(symb, new Effect_StaticData()) );
		//... add initializer effect if it exists.
		  if( (*it)->get_initptr() != NULL ) {
		      SgAssignInitializer *assInit = isSgAssignInitializer((*it)->get_initptr());
		      ROSE_ASSERT(assInit != NULL);
		      FT::Common::SymbDesc *symEff = dynamic_cast<FT::Common::SymbDesc *>(c->getNamedLoc(assInit->get_operand_i()));
	              #if FT_DEBUG_TRANSFORM > 2
	      	    	  cout << "(VarDecl-Init.) Added effect (" << FT::Common::toString(symb) << ", " << FT::Common::toString(symEff) << ")" << endl;
       	              #endif
		      effects.push_back( new FT::Common::EffectVal(symb, new Effect_Symbolic(symEff) ) );
		  }
	  }
	  SgNode *n = transformSingle(effects, c, cs, globalScope);
	  #if FT_DEBUG_TRANSFORM > 3
		cout << "Output VarDecl: ";
		if(n != NULL) {
		   cout << n->class_name() << " (" << n << ") X{" << endl;
		   if(isSgBasicBlock(n) != NULL)
		      for(SgStatementPtrList::iterator it = static_cast<SgBasicBlock *>(n)->get_statements().begin();
			    it != static_cast<SgBasicBlock *>(n)->get_statements().end();
			    ++it)
				cout << (*it)->unparseToString() << endl;
		   cout << "}X" << endl;
		} else
		   cout << "NULL " << endl;
	  #endif
	  return n;
       } else if(TInterface::IsCase(inputNode, &stmBody, NULL)) {
	  #if FT_DEBUG_TRANSFORM > 0
	      cout << "[Transform-Case] ";
	      #if FT_DEBUG_TRANSFORM > 4
	      	  cout << inputNode->unparseToString();
       	      #endif
	      cout << endl;
       	  #endif
	  SgStatement *stm = isSgStatement( transformSingle(stmBody, c, cs, globalScope) );
	  TInterface::SetCase(inputNode, stm, NULL);
	  #if FT_DEBUG_TRANSFORM > 3
	  	cout << "Output Case: ";
		if(stm != NULL)
		   cout << stm->class_name() << " (" << stm << ")" << endl;
		else
			cout << "NULL" << endl;
	  #endif
	  return inputNode;
       } else if(TInterface::IsBlock(inputNode, &stmBodyList, NULL)) {
	  SgBasicBlock *bb = SageBuilder::buildBasicBlock();
	  Closure *cC = c->child();
          for(Rose_STL_Container<SgStatement*>::iterator it = stmBodyList->begin(); it != stmBodyList->end(); ++it) {
              SgStatement *stm = isSgStatement( transformSingle(*it, cC, cs, globalScope) );
	      if(stm != NULL)
	         SageInterface::appendStatement(stm, bb);
          }
	  bb = appendStatement(bb, cC->kill());
	  #if FT_DEBUG_TRANSFORM > 3
	  	cout << "Output Block: " << bb << endl;
	  #endif
	  return bb;
       } else if(TInterface::IsStatement(inputNode)) {
	  #if FT_DEBUG_TRANSFORM > 0
	      cout << "[Transform-Stm.] ";
	      #if FT_DEBUG_TRANSFORM > 4
	      	  cout << inputNode->unparseToString();
       	      #endif
       	  #endif
	SgStatement *stm = isSgStatement(inputNode);
	//Run side-effect analysis...
       	  vector< SgNode * > rVars, wVars;
     	  //Collect R/W list...
       	    if(!SageInterface::collectReadWriteRefs(stm, rVars, wVars)) {
          	  #ifdef FT_POST_ERROR_MSG_AS_SRC_COMMENT
               		 SageInterface::attachComment(stm, "Unmodified statement: " + stm->unparseToString() + " (Couldn't decide side-effects)");
          	  #endif
	  	  #if FT_DEBUG_TRANSFORM > 0
	      		cout << " collectReadWriteRefs() failed." << endl;
       	  	  #endif
          	  return inputNode;
       	    }
       	    if(wVars.size() != 1) {
          	  #ifdef FT_POST_ERROR_MSG_AS_SRC_COMMENT
		       	string str("Invalid number of write references {");
		       	for(unsigned int i = 0; i < wVars.size(); i++) {
		            	str.append("'" + wVars[i]->unparseToString() + "'");
		            	if(i < wVars.size()-1)
		                 	str.append(", ");
		       	}                    
		       	SageInterface::attachComment(stm, "Unmodified statement: " + stm->unparseToString() + " (" + str + "})");
          	  #endif
	  	  #if FT_DEBUG_TRANSFORM > 0
	      		cout << str << endl;
       	  	  #endif
          	  return inputNode;
       	    }

	    vector<FT::Common::EffectVal *> effects;
       	    SgExpression *exp;
       	    /*This wouldn't be a problem if the side-effect analysis returned a pair <e,s> for
              each side-effect. Where 'e' is the destination of the side-effect and 's' is a symbolic
	      representation of the side-effect itself */
       	    switch(stm->variantT()) {
             case V_SgExprStatement: 
		exp = static_cast<SgExprStatement *>(stm)->get_expression();
		if(isSgCompoundAssignOp(exp) != NULL)
			exp = static_cast<SgCompoundAssignOp *>(exp)->get_rhs_operand();
		else
			switch(exp->variantT()) {
			 case V_SgMinusMinusOp:	exp = SageBuilder::buildBinaryExpression<SgSubtractOp>(
							static_cast<SgUnaryOp *>(exp)->get_operand(),
							BInterface::buildConstant(exp->get_type(), 1.0));
						break;
			 case V_SgPlusPlusOp:	exp = SageBuilder::buildBinaryExpression<SgAddOp>(
							static_cast<SgUnaryOp *>(exp)->get_operand(),
							BInterface::buildConstant(exp->get_type(), 1.0));
						break;
			 case V_SgAssignOp:	exp = static_cast<SgAssignOp *>(exp)->get_rhs_operand();
						break;
			 default:
			       	#ifdef FT_POST_ERROR_MSG_AS_SRC_COMMENT
				   SageInterface::attachComment(stm, "(Unhandled exp type '" + exp->class_name() + "')");
			       	#endif
			  	#if FT_DEBUG_TRANSFORM > 0
			      	   cout << "Unhandled exp type '" + exp->class_name() + "'." << endl;
		       	  	#endif
				break;
			}
		break;
             default:
               	#ifdef FT_POST_ERROR_MSG_AS_SRC_COMMENT
                   SageInterface::attachComment(stm, "(Unhandled stm type '" + stm->class_name() + "')");
               	#endif
	  	#if FT_DEBUG_TRANSFORM > 0
	      	   cout << "Unhandled stm type '" + stm->class_name() + "'." << endl;
       	  	#endif
		return inputNode;
       	    }
	    #if FT_DEBUG_TRANSFORM > 2
	        cout << " {";
       	    #endif
       	    for(vector< SgNode * >::iterator it = wVars.begin(); it != wVars.end(); ++it) {
		//Get destionation of symbol...
                  SgExpression *ref = isSgExpression( *it );
                  ROSE_ASSERT(ref != NULL);
	          FT::Common::SymbDesc *sym = dynamic_cast<FT::Common::SymbDesc *>(c->getNamedLoc(ref));
		//Create effect structure...
		  FT::Common::SymbDesc *effSym = dynamic_cast<FT::Common::SymbDesc *>(c->getNamedLoc(exp));
		  ROSE_ASSERT(effSym != NULL);
	          FT::Common::Effect *eff = new Effect_Symbolic(effSym);
	          #if FT_DEBUG_TRANSFORM > 2
	      	    cout << "Added effect (" << FT::Common::toString(sym) << ", " << *eff << "), ";
       	          #endif

	          effects.push_back( new FT::Common::EffectVal(sym, eff) );
       	    }
	    #if FT_DEBUG_TRANSFORM > 2
	        cout << "}";
       	    #endif
	    #if FT_DEBUG_TRANSFORM > 0
	        cout << endl;
       	    #endif
	//Invoke handler...
	  SgNode *n = transformSingle(effects, c, cs, globalScope);
	  #if FT_DEBUG_TRANSFORM > 3
	  	cout << "Output Stm (" << n << "): " ;
		#if FT_DEBUG_TRANSFORM > 4
	  	    SgBasicBlock *bb = isSgBasicBlock(n);
		    if(bb != NULL) {
			for(SgStatementPtrList::iterator it = bb->get_statements().begin();
			    it != bb->get_statements().end();
			    ++it)
				cout << (*it)->unparseToString() << endl;
		    } else
			cout << n->unparseToString() << endl;
		#else
			cout << "NULL" << endl;
		#endif
	  #endif
	  return n;
       } else {
             stringstream ss;
             ss << "Unhandled node '" << inputNode->class_name() << "'.";
             throw FT::Common::FTException(ss.str());
       }                              
}


SgNode *FT::Transform::transformMulti(ControlStruct &cs, SgNode *inputNode, FT::Common::FTVisitor *decisionFunctor, SgGlobal *globalScope) {
     //Determine global scope...
       SgGlobal *gScope = globalScope;
       if(isSgStatement(inputNode) != NULL) 
          gScope = (gScope == NULL ?
                    (this->globalScope == NULL ? SageInterface::getGlobalScope(static_cast<SgStatement *>(inputNode)) : this->globalScope) :
                    gScope);
     //Create default collector...
       if(decisionFunctor == NULL)
          decisionFunctor = new FTPragmaVisitor();
     //Collect nodes...
       if(inputNode == NULL)
          decisionFunctor->traverseMemoryPool();
       else
          decisionFunctor->traverse(inputNode);
     //Remove selected nodes...
       for(std::vector<SgNode *>::iterator it = decisionFunctor->getRemoveNodes().begin();
           it != decisionFunctor->getRemoveNodes().end();
           ++it) {
		SgStatement *stm = isSgStatement( *it );
                if(stm != NULL)
                    SageInterface::removeStatement( stm );
                else
                    SageInterface::deleteAST( *it );

		#if FT_DEBUG_TRANSFORM > 3
			cout << "REMOVED---------------------------------------------------" << endl
			     << (*it)->unparseToString() << endl
			     << "----------------------------------------------------------" << endl;
		#endif
       }
     //Transform selected nodes...
       SgNode *outputNode = inputNode, *tmpNode;
       for(std::vector<SgNode *>::iterator it = decisionFunctor->getTargetNodes().begin();
           it != decisionFunctor->getTargetNodes().end();
           ++it) {
                    //Transform node
		      Closure *c = new Closure();
                      if((tmpNode = transformSingle( *it, c, cs, gScope)) == NULL)
			  tmpNode = *it;
                    //Replace stm...               
                      if(*it != tmpNode) {
                         SgStatement *oldStm = isSgStatement(*it), *newStm = isSgStatement(tmpNode);
                         ROSE_ASSERT(oldStm != NULL && newStm != NULL);
                         SageInterface::insertStatement(oldStm, newStm);
                         SageInterface::removeStatement(oldStm);
			 #if FT_DEBUG_TRANSFORM > 3
			     cout << "CHANGED--------------------OLD----------------------------" << endl
			          << oldStm->unparseToString() << endl;
			     cout << "CHANGED--------------------NEW----------------------------" << endl
			          << newStm->unparseToString() << endl
			          << "----------------------------------------------------------" << endl;
			 #endif
                      }
		    //Add closure declarations...
		      SgBasicBlock *bb = c->kill();
		      if(bb != NULL)
			 tmpNode = appendStatement(isSgStatement(tmpNode), bb);
		    //Did we change input node?
                      if(*it == inputNode)
                         outputNode = tmpNode;
       }

     if(isSgStatement(outputNode) != NULL)
        cout << "OUTPUT:" << endl 
	     << "----------------------------------------------------------" << endl
	     << isSgStatement(outputNode)->unparseToString() << endl
	     << "----------------------------------------------------------" << endl;
     return outputNode;
}

void FT::Transform::revokeEffects(Closure *c, vector<FT::Common::EffectVal *> &effects) {
	for(vector<FT::Common::EffectVal *>::iterator it = effects.begin();
	    it != effects.end();
	    ++it) {
		//TODO! Remove shadow register if one is found...
		  FT::Common::Region_Desc *rD = (*it)->s->getRegion();

		//Reclaim memory space...
		  //delete *it;
	}
}

