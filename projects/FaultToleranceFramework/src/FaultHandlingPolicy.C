#include <iostream>
#include <map>
#include <vector>

#include "rose.h"
#include "OmpAttribute.h"

#include "TI.h"
#include "Transform/ft_transform.h"

///////////////////////////////////////// ControlStruct_Check /////////////////////////////////////////
SgExpression *FT::Transform::ControlStruct_Check::Comparator::getHandler(VariantT compOp, SgType *expType, SgExpression *lhs, SgExpression *rhs) {
	//Decide wheather to compare the var or the addr. of the var...
	  bool useAddr = TInterface::IsTerminalVariable(lhs) && TInterface::IsTerminalVariable(rhs) && adjUseAddrOfVar(expType);
	  SgExpression *lhs_ = (useAddr ? SageBuilder::buildUnaryExpression<SgAddressOfOp>(lhs) : lhs),
			*rhs_ = (useAddr ? SageBuilder::buildUnaryExpression<SgAddressOfOp>(rhs) : rhs);
	//Return a comparator...
	  switch(compOp) {
	   case V_SgEqualityOp:			return SageBuilder::buildBinaryExpression<SgEqualityOp>(lhs_, rhs_);
	   case V_SgGreaterOrEqualOp:		return SageBuilder::buildBinaryExpression<SgGreaterOrEqualOp>(lhs_, rhs_);
	   case V_SgGreaterThanOp:		return SageBuilder::buildBinaryExpression<SgGreaterThanOp>(lhs_, rhs_);
	   case V_SgLessOrEqualOp:		return SageBuilder::buildBinaryExpression<SgLessOrEqualOp>(lhs_, rhs_);
	   case V_SgLessThanOp:			return SageBuilder::buildBinaryExpression<SgLessThanOp>(lhs_, rhs_);
	   case V_SgNotEqualOp:			return SageBuilder::buildBinaryExpression<SgNotEqualOp>(lhs_, rhs_);
	   default:
			throw FT::Common::FTException("Invalid comparator operator.");
	  }
}
bool FT::Transform::ControlStruct_Check::Comparator::adjUseAddrOfVar(SgType *t) {
	switch(t->variantT()) {
	 case V_SgArrayType:		return true;
	 case V_SgFunctionType:		return true;
	 case V_SgModifierType:		return static_cast<SgModifierType *>(t)->get_base_type();
	 case V_SgPointerType:			return false;
	 case V_SgQualifiedNameType:		return static_cast<SgQualifiedNameType *>(t)->get_base_type();
	 case V_SgReferenceType:			return true;
	 case V_SgTypeBool:				return false;
	 case V_SgTypeChar:				return false;
	 case V_SgTypeComplex:			return false;
	 case V_SgTypeCrayPointer:		return false;
	 case V_SgTypeDouble:			return false;
	 case V_SgTypeEllipse:			return false;
	 case V_SgTypeFloat:			return false;
	 case V_SgTypeImaginary:			return false;
	 case V_SgTypeInt:				return false;
	 case V_SgTypeLabel:			return true;
	 case V_SgTypeLong:				return false;
	 case V_SgTypeLongDouble:		return false;
	 case V_SgTypeLongLong:			return false;
	 case V_SgTypeShort:			return false;
	 case V_SgTypeSignedChar:		return false;
	 case V_SgTypeSignedInt:			return false;
	 case V_SgTypeSignedLong:		return false;
	 case V_SgTypeSignedLongLong:		return false;
	 case V_SgTypeSignedShort:		return false;
	 case V_SgTypeString:			return false;
	 case V_SgTypeUnsignedChar:		return false;
	 case V_SgTypeUnsignedInt:		return false;
	 case V_SgTypeUnsignedLong:		return false;
	 case V_SgTypeUnsignedLongLong:	return false;
	 case V_SgTypeUnsignedShort:		return false;			
	 case V_SgTypeWchar:			return false;

	 case V_SgTemplateType:	 
	 case V_SgNamedType:		
	 case V_SgTypeCAFTeam:	
	 case V_SgTypeDefault:
	 case V_SgTypeGlobalVoid:
	 case V_SgTypeUnknown:	
	 case V_SgTypeVoid:
	 default:
			cout << "Unhandled type '" << t->class_name() << "'." << endl;
			ROSE_ASSERT(false); //unhandled case
	}
}

pair<SgExpression *, SgStatement *> FT::Transform::ControlStruct_Check::getCond(Closure *declClos, vector<FT::Common::EffectVal *> &evList) {
     stack<SgExpression *> operandStack[2];
     set<SgExpression *> wVars;
     SgExpression *lhs, *rhs, *finalExp = NULL;
     SgAndOp *lastExp = NULL;

     if(evList.size() == 0)
	return pair<SgExpression *, SgStatement *>(SageBuilder::buildBoolValExp(true), NULL);

     //Create comp. exp for each variable
       for(vector<FT::Common::EffectVal *>::iterator it = evList.begin(); it != evList.end(); ++it) {
	  //Initialization...
	    FT::Common::Effect_Symbolic *eff = dynamic_cast<FT::Common::Effect_Symbolic *>((*it)->e);
	    FT::Transform::SymbDesc *sym = dynamic_cast<FT::Transform::SymbDesc *>((*it)->s);
	    //Setup initial value for this pair
	      wVars.clear();
              if((sym == NULL) || (eff == NULL) || !sym->getLHS(wVars, 0, eff->effect.size()) || (wVars.size() == 0))
                 continue;
	    SgType *symType = sym->getRegion()->getType();
          //Put all SgVarRefExp (enteries in wVars) on stack...
            for(set<SgExpression *>::iterator it = wVars.begin(); it != wVars.end(); ++it)
                     operandStack[0].push( *it );
          //Group stack elements linearly and create SgEqualityOp of each pair...
          //(ex. {1,2,3,4,5,...} -> {<1,2>,<2,3>,<3,4>,...}
            if(operandStack[0].size() > 1) {
               lhs = operandStack[0].top(); operandStack[0].pop();
               while(operandStack[0].size() > 0) {
                     rhs = operandStack[0].top(); operandStack[0].pop();
                     operandStack[1].push( c->getHandler(V_SgEqualityOp, symType, lhs, rhs) );
                     lhs = rhs;
               }
            } else {
                    operandStack[1].push( operandStack[0].top() ); 
                    operandStack[0].pop();
            }
          //Create a conjunction clause/chain with each ==
            if(operandStack[1].size() > 1) {
               if(lastExp == NULL) {
                  rhs = operandStack[1].top(); operandStack[1].pop();
                  finalExp = lastExp = SageBuilder::buildBinaryExpression<SgAndOp>(NULL, rhs);
               }
               while(operandStack[1].size() > 0) {
                     rhs = operandStack[1].top(); operandStack[1].pop();
                     lastExp->set_lhs_operand_i(SageBuilder::buildBinaryExpression<SgAndOp>(NULL, rhs));
                     lastExp->get_lhs_operand_i()->set_parent(lastExp);
                     lastExp = isSgAndOp( lastExp->get_lhs_operand_i() );
               }
            } else {
                    if(lastExp == NULL)
                       finalExp = lastExp = SageBuilder::buildBinaryExpression<SgAndOp>(NULL, operandStack[1].top() );
                    else {
                          lastExp->set_lhs_operand_i( SageBuilder::buildBinaryExpression<SgAndOp>(NULL, operandStack[1].top()) );
                          lastExp->get_lhs_operand_i()->set_parent(lastExp);
                          lastExp = isSgAndOp( lastExp->get_lhs_operand_i() );
                    }
                    operandStack[1].pop();
            }
       }
     //Handle the end of the conj. chain
       if(lastExp == NULL)
	  return pair<SgExpression *, SgStatement *>(NULL, NULL);
       if(lastExp->get_parent() != NULL) {
          SgAndOp *opAndRhs = isSgAndOp(lastExp->get_parent());
          opAndRhs->set_lhs_operand_i(lastExp->get_rhs_operand_i());
       } else
             finalExp = lastExp->get_rhs_operand_i();
       lastExp->set_rhs_operand_i(NULL);
       SageInterface::deleteAST(lastExp);
     //Return expression...make debug
       ROSE_ASSERT(finalExp != NULL);
       return pair<SgExpression *, SgStatement *>(finalExp, NULL);
}

SgStatement *FT::Transform::ControlStruct_Check::getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList) {
	pair<SgExpression *, SgStatement *> cond = this->getCond(declClos, evList);
	if(cond.first == NULL)
	   return NULL;
	#if FT_DEBUG_TRANSFORM > 0
	   	cout << "[Check-" << this << "] <" << cond.first->unparseToString();
		if(cond.second == NULL)
			cout << ", NULL>, ";
		else
			cout << ", " << cond.second->unparseToString() << ">, ";
		if(this->faultCase != NULL)
			cout << "<Fault: " << this->faultCase << ">, ";
		if(this->properCase != NULL)
			cout << "<Proper: " << this->properCase << ">, ";
		cout << endl;
       	#endif
	//Create IF-structure...
	  SgIfStmt *stmIf;
	  if(this->faultCase == NULL) {
		if(this->properCase == NULL)
		   ROSE_ASSERT(false);
		else
			stmIf = SageBuilder::buildIfStmt(
       					SageBuilder::buildExprStatement(cond.first),
       					this->properCase->getHandler(declClos, evList), 
					NULL);
	  } else {
		if(this->properCase == NULL)
			stmIf = SageBuilder::buildIfStmt(
       					SageBuilder::buildExprStatement(SageBuilder::buildUnaryExpression<SgNotOp>(cond.first)),
       					this->faultCase->getHandler(declClos, evList), 
					NULL);
	  	else
			stmIf = SageBuilder::buildIfStmt(
       					SageBuilder::buildExprStatement(cond.first),
					this->properCase->getHandler(declClos, evList),
       					this->faultCase->getHandler(declClos, evList));
	  }
	//Did we require any extra statement?
	  if(cond.second == NULL)
		return stmIf;
	  else {
		SgBasicBlock *bb = SageBuilder::buildBasicBlock();
		appendStatement(cond.second, bb);
		appendStatement(stmIf, bb);
		return bb;
	  }
};

///////////////////////////////////////// ControlStruct_Adjudicator /////////////////////////////////////////

FT::Transform::ControlStruct_Adjudicator::ControlStruct_Adjudicator(Adjucator *adj, ControlStruct *secondCS) {
	if(adj == NULL)
		this->adj = new Adjucator_Meta();
	else
		this->adj = adj;
	this->secondCS = secondCS;
}


//Control structure "Adjucator" - Decide which result to choose from
SgStatement *FT::Transform::ControlStruct_Adjudicator::getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList) {
     SgBasicBlock *bb = SageBuilder::buildBasicBlock();

     if(this->adj == NULL)
          throw FT::Common::FTException("No adjudicator set");

     #if FT_DEBUG_TRANSFORM > 0
	cout << "[Adjucator-" << this << "] " << this->adj << ", " << evList.size() << " {" << endl;
     #endif

     //Create handler for each 
       vector<FT::Common::EffectVal *> rmVec;
       for(vector<FT::Common::EffectVal *>::iterator it = evList.begin(); it != evList.end(); ) { 
       	 //Initialization...
	   SymbDesc *symb = dynamic_cast<SymbDesc *>( (*it)->s );
	   Effect_Symbolic *effSym = dynamic_cast<Effect_Symbolic *>( (*it)->e );
	   if( (symb == NULL) || (effSym == NULL) || (effSym->effect.size() <= 1) ) {
	      ++it;
	      #if FT_DEBUG_TRANSFORM > 0
		  cout << "Ignoring effect " << (*it)->s << endl;
	      #endif
	      continue;
	   }
	 //Perform operation...
	   SgStatement *sg = adj->getHandler(declClos, *it, secondCS);
	   if(sg != NULL) {
           	appendStatement(sg, bb);
	   	rmVec.push_back(*it);
	   	it = evList.erase(it);
	   }
       }
     //Remove handled effects...
       revokeEffects(declClos, rmVec);

     #if FT_DEBUG_TRANSFORM > 0
	cout << "}" << endl;
     #endif

     return bb;
}

//Adjucator "Meta" - 
unsigned long FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorDec::operator()(Closure *declClos, FT::Common::EffectVal *effect) {
	SymbDesc *symb = dynamic_cast<SymbDesc *>(effect->s);
	if(symb == NULL)
	   return 0;
	SgType *mType = symb->getRegion()->getType();
	if(mType == NULL)
	   return 0;
	switch(mType->variantT()) {
	 //Composite types...
	   case V_SgArrayType:
	   case V_SgFunctionType:
	   case V_SgMemberFunctionType:
	   case V_SgPartialFunctionType:
	   case V_SgPartialFunctionModifierType:
	   case V_SgNamedType:
	   case V_SgClassType:
	   case V_SgPointerType:
	   case V_SgPointerMemberType:
	   case V_SgReferenceType:
	   case V_SgTemplateType:			return 1;
	 //Floating-point types
	   case V_SgTypeComplex:
	   case V_SgTypeDouble:
	   case V_SgTypeEllipse:
	   case V_SgTypeFloat:
	   case V_SgTypeLongDouble:			return 2;
	 //Interger types
	   default:					return 3;
	}
}

FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::Adjucator_Meta(AdjucatorDec &dAdj, AdjucatorMech &mAdj) :
	decAdj(dAdj), mechAdj(mAdj)  {}

SgStatement *FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::getHandler(Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS) {
	#if FT_DEBUG_TRANSFORM > 1
	   	cout << "[Adjucator-Meta-" << this << "] <" << &mechAdj << ", " << &decAdj << ">" << endl;
       	#endif
	return mechAdj.getHandler( decAdj(declClos, effect), declClos, effect, secondCS);
}

FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorMech::AdjucatorMech(unsigned long condClass, AdjucatorMech *a, AdjucatorMech *f, bool deleteWhenDone) {
	ROSE_ASSERT(a != NULL);
	ROSE_ASSERT(f != NULL);
	this->accept = a;
	this->fail = f;
	this->condClass = condClass;
	this->deleteWhenDone = deleteWhenDone;
}
FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorMech::~AdjucatorMech() {
	if(deleteWhenDone) {
		delete this->accept;
		delete this->fail;
	}
}
SgStatement *FT::Transform::ControlStruct_Adjudicator::Adjucator_Meta::AdjucatorMech::getHandler(unsigned long cat, Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS) {
	#if FT_DEBUG_TRANSFORM > 2
	   	cout << "Category: '" << cat << "' => ";
       	#endif
	if(this->condClass == cat) {
		#if FT_DEBUG_TRANSFORM > 2
	   		cout << "Accept path taken." << endl;
       		#endif
                return accept->getHandler(cat, declClos, effect, secondCS);
        } else {
		#if FT_DEBUG_TRANSFORM > 2
	   		cout << "Fail path taken." << endl;
       		#endif
                return fail->getHandler(cat, declClos, effect, secondCS);
        }
}

//////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////// Non-terminal control structures. //////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////
 
//Control structure "Final wish" - Invokes a given statement before (optionally) calling a next-level handler
SgStatement *FT::Transform::ControlStruct_FinalWish::getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList) {
	SgBasicBlock *bb = SageBuilder::buildBasicBlock();
     //Inject statement
       appendStatement(stm, bb);
       #if FT_DEBUG_TRANSFORM > 0
	   cout << "[FinalWish-" << this << "] Added '" << stm->unparseToString() << "'." << endl;
       #endif
     //Perform second level handler...
       if(sLv != NULL) {  
	  #if FT_DEBUG_TRANSFORM > 0
	   	cout << "[FinalWish-" << this << "] Calling 2nd handler (" << sLv << ") {" << endl;
       	  #endif
	  appendStatement(sLv->getHandler(declClos, evList), bb);
	  #if FT_DEBUG_TRANSFORM > 0
	   	cout << "}" << endl;
       	  #endif
       }
     return bb;
}

//Control structure "Second chance" - Perform the computation upto N times while fault occurs, before (optionally) calling next level handler
SgStatement *FT::Transform::ControlStruct_SecondChance::getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList) {
     //Error check
       ROSE_ASSERT(cs != NULL);
       ROSE_ASSERT(es != NULL);
     //Initialize
       SgBasicBlock *bb = SageBuilder::buildBasicBlock();
     //Create for loop...
       declClos->addNamedLoc(SgName("rI"), 1, NULL, SageBuilder::buildIntType());

       SgForStatement *forStmExec = SageBuilder::buildForStatement(
          SageBuilder::buildAssignStatement(
		SageBuilder::buildVarRefExp(SgName("rI")), 
		SageBuilder::buildIntVal(0)),
          SageBuilder::buildExprStatement(SageBuilder::buildBoolValExp(true)),
          SageBuilder::buildBinaryExpression<SgPlusAssignOp>(
		SageBuilder::buildVarRefExp(SgName("rI")), 
		SageBuilder::buildIntVal(1)),
          bb);
	//Add CS handler routine...
          #if FT_DEBUG_TRANSFORM > 0
	      cout << "[SecondChance-" << this << "] CS: {" << endl;
          #endif
	  SgStatement *stmCS = cs->getHandler(declClos, evList);
	  appendStatement(stmCS, bb);
          #if FT_DEBUG_TRANSFORM > 0
	   	cout << "} ES: {" << endl;
       	  #endif
     //Create condition checker...
	  pair<SgExpression *, SgStatement *> esPair = es->getCond(declClos, evList);
	  if(esPair.second != NULL)
	  	appendStatement(esPair.second, bb);
	  SgStatement *stm;
          #if FT_DEBUG_TRANSFORM > 0
	   	cout << "} FS: {" << endl;
       	  #endif
	  if(fs == NULL)
		stm = SageBuilder::buildBreakStmt();
	  else
		stm = SageBuilder::buildBasicBlock(fs->getHandler(declClos, evList), SageBuilder::buildBreakStmt());
          #if FT_DEBUG_TRANSFORM > 0
	   	cout << "}" << endl;
       	  #endif
       appendStatement(
          SageBuilder::buildIfStmt(
               SageBuilder::buildExprStatement(esPair.first),
               SageBuilder::buildBreakStmt(),
               SageBuilder::buildIfStmt(
                    SageBuilder::buildExprStatement(
                         SageBuilder::buildUnaryExpression<SgNotOp>(
                              SageBuilder::buildBinaryExpression<SgLessThanOp>(
                                   SageBuilder::buildVarRefExp(SgName("rI")),
                                   SageBuilder::buildIntVal(N)))),
                    stm, NULL)),
          bb);
     return forStmExec;
}

//Control structure "Composition" - Use multiple CS's in sequence
SgStatement *FT::Transform::ControlStruct_Composition::getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList) {
	SgBasicBlock *bb = SageBuilder::buildBasicBlock();
	//Add all statements...
	  #if FT_DEBUG_TRANSFORM > 0
	   	cout << "[Composition-" << this << "] " << cs.size() << " CS's ..." << endl;
		unsigned int i = 0;
       	  #endif
	  for(vector<ControlStruct *>::iterator it = cs.begin(); it != cs.end(); ++it) {
		 #if FT_DEBUG_TRANSFORM > 0
		 	cout << "CS #" << i << " {" << endl;
			i++;
	       	 #endif
		 appendStatement( (*it)->getHandler(declClos, evList), bb );
		 #if FT_DEBUG_TRANSFORM > 0
		 	cout << "}" << endl;
	       	 #endif
	  }
	return bb;
}

//////////////////////////////////////////////////////////////////////////////////////////////////////
////////////////////////////////////// Terminal fault handlers ///////////////////////////////////////
//////////////////////////////////////////////////////////////////////////////////////////////////////

//Control structure "Redundant execute" - Replicate computation N times (optionally transforming the effect)
SgStatement *FT::Transform::ControlStruct_RedundantExec::getHandler(Closure *declClos, vector<FT::Common::EffectVal *> &evList) {
	SgBasicBlock *bb = SageBuilder::buildBasicBlock();

	#if FT_DEBUG_TRANSFORM > 0
	   	cout << "[Redundant-" << this << "] " << evList.size() << " {" << endl;
		unsigned int i = 0;
       	#endif
	for(vector<FT::Common::EffectVal *>::iterator it = evList.begin(); it != evList.end(); ++it) {
	    //Make sure we're dealing with a symbolic effect...
	      #if FT_DEBUG_TRANSFORM > 0
	   	cout << i << "-" << *it;
       	      #endif
	      FT::Common::SymbDesc *symbCommon = (*it)->s;
	      SymbDesc *symbTransform = dynamic_cast<SymbDesc *>( symbCommon );
	      Effect_Symbolic *effSym = dynamic_cast<Effect_Symbolic *>( (*it)->e );
	      if( (symbTransform == NULL) || (effSym == NULL) ) {
		 cout << "(RedundantExec-" << this << ") Ignoring effect " << *(*it) << endl;
		 continue;
	      }
	    //Decide parameters...
	      vector<FT::Common::SymbDesc *> tmpArray;
	      unsigned int iEnd, iStart;
	      if(this->Na > effSym->effect.size()) { //Absolute
		  iEnd = this->Na;
		  iStart = 0;

		  std::fill(effSym->transformedEffects.begin(), effSym->transformedEffects.end(), false);
	          #if FT_DEBUG_TRANSFORM > 0
	   		cout << " (Absolute) ";
       	          #endif
	      } else if(this->Nr > 0.0) { //Relative
		  iEnd = round((1.0+this->Nr) * effSym->effect.size());
		  iStart = effSym->effect.size();

		  tmpArray.insert(tmpArray.begin(), effSym->effect.begin(), effSym->effect.end());
	          #if FT_DEBUG_TRANSFORM > 0
	   		cout << " (Relative) ";
       	          #endif
	      } else {
		  #if FT_DEBUG_TRANSFORM > 0
	   		cout << "(RedundantExec-" << this << ") Ignoring effect (Neither absolute nor relative value valid)" << endl;
       	          #endif
		  continue;
	      }
	    //Replicate effect
	      for(unsigned int i = iStart; i < iEnd; i++) {	 
		  unsigned int rndIndex = FT::Common::Singleton::getInstance().getRandomInt(0, effSym->effect.size());
		  FT::Common::SymbDesc *exp = (this->effTrans != NULL ? this->effTrans->transform(i, symbCommon, effSym->effect[rndIndex]) : effSym->effect[rndIndex]);
		  tmpArray.push_back(exp);
	      }
	    //Update effect...
	      effSym->effect.clear();
	      effSym->effect.insert(effSym->effect.begin(), tmpArray.begin(), tmpArray.end());
	    //Get destination symbol...
       	      FT::Common::Region_Desc *regDest = upgrade(declClos, declClos->lessSafe(symbCommon->getRegion(), iEnd-iStart+1));
	      (*it)->s = regDest->getSymbol();
       	      FT::Transform::SymbDesc *symDest = dynamic_cast<FT::Transform::SymbDesc *>((*it)->s);
	      symDest->setN( iEnd-iStart+1 );
       	      ROSE_ASSERT(symDest != NULL);
	    //Insert effect in implementation
	      vector<SgStatement *> stmList;
	      effSym->transform(declClos, stmList, symDest);
	      SageInterface::appendStatementList(stmList, bb);
	    //TODO! Handle assignment back to original location using naming scheme...
	      SageInterface::appendStatement(
			SageBuilder::buildAssignStatement(
				symbTransform->project(0),
				symDest->project(FT::Common::Singleton::getInstance().getRandomInt(0, iEnd-iStart)) ), bb);

	      #if FT_DEBUG_TRANSFORM > 0
		cout << " {";
		for(unsigned int i = 0; i < stmList.size(); i++)
			cout << stmList[i]->unparseToString() << ", ";
		cout << "}" << endl;
	      #endif
	      
	}

	return bb;	
}

//Fault policy "Voting" - Vote on the results
SgStatement *FT::Transform::Adjucator_Voting_Mean::getHandler(Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS) {
     //Make sure we're dealing with a symbolic effect...
       SymbDesc *symb = dynamic_cast<SymbDesc *>(effect->s);
       Effect_Symbolic *effSym = dynamic_cast<Effect_Symbolic *>( effect->e );
       if( (symb == NULL) || (effSym == NULL) ) {
	    cout << "(Adjucator_Mean-" << this << ") Ignoring effect " << *effect << endl;
	    return NULL;
       }
     //Initialize
       set<SgExpression *> updatedValues;
       if(!symb->getLHS(updatedValues, 0, effSym->effect.size()) || (updatedValues.size() == 0))
          return NULL;
       SgExpression *value = *(updatedValues.begin()), *lhs;
       SgType *baseType = symb->getRegion()->getType();
       if(weights.size() > 0)
          lhs = SageBuilder::buildBinaryExpression<SgMultiplyOp>(
                	SageBuilder::buildDoubleVal(this->weights[0]), 
                        value);
       else
	  lhs = value;
       #if FT_DEBUG_TRANSFORM > 0
	   cout << "[Adjucator-Mean-" << this << "] \"" << toString(symb) << "\" = {" ;
	   for(set<SgExpression *>::iterator it2 = updatedValues.begin(); it2 != updatedValues.end(); ++it2)
	       cout << (*it2)->unparseToString() << ", ";
	   cout << "}" << endl;
       #endif
     //Create a sum of all the expressions...
       SgAddOp *addOp = SageBuilder::buildBinaryExpression<SgAddOp>(lhs, NULL), *firstAddOp = addOp;
       for(set<SgExpression *>::iterator it2 = ++updatedValues.begin();
           it2 != updatedValues.end();
           ++it2) {
                   if(weights.size() == 0)
                      value = *it2;
                   else {
                      value = SageBuilder::buildBinaryExpression<SgMultiplyOp>(
                                   SageBuilder::buildDoubleVal(weights[0]), 
                                   *it2);
		      weights.erase(weights.begin());
		   }
                   addOp->set_rhs_operand_i( SageBuilder::buildBinaryExpression<SgAddOp>(value, NULL) );
                   addOp->get_rhs_operand_i()->set_parent(addOp);
                   addOp = isSgAddOp( addOp->get_rhs_operand_i() );
       }
     //Finalize the expression
       if(addOp->get_parent() != NULL) {
          SgAddOp *addOpParent = isSgAddOp(addOp->get_parent());
          addOpParent->set_rhs_operand_i(addOp->get_lhs_operand_i());
       } else
             addOp = isSgAddOp(addOp->get_lhs_operand_i());
       addOp->set_lhs_operand_i(NULL);
       SageInterface::deleteAST(addOp);
     //Get destination symbol...
       FT::Common::Region_Desc *regDest = declClos->moreSafe(symb->getRegion(), 1);
       FT::Transform::SymbDesc *symDest = dynamic_cast<FT::Transform::SymbDesc *>(regDest->getSymbol());
       ROSE_ASSERT(symDest != NULL);

     return SageBuilder::buildExprStatement(
               SageBuilder::buildBinaryExpression<SgAssignOp>(
                              symDest->project(0), 
                              SageBuilder::buildBinaryExpression<SgDivideOp>(
                                  firstAddOp, 
                                  BInterface::buildConstant(baseType, updatedValues.size()) )));
}

SgStatement *FT::Transform::Adjucator_Voting_Median::getHandler(Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS) {
     //Make sure we're dealing with a symbolic effect...
       SymbDesc *symb = dynamic_cast<SymbDesc *>(effect->s);
       Effect_Symbolic *effSym = dynamic_cast<Effect_Symbolic *>(effect->e);
       if( (symb == NULL) || (effSym == NULL) ) {
	  cout << "(Adjucator_Median-" << this << ") Ignoring effect " << *effect << endl;
	  return NULL;
       }
     //Initialize
       SgType *baseType = symb->getRegion()->getType();
       bool useAddr = c->adjUseAddrOfVar(baseType);
       set<SgExpression *> updatedValues;
       if(!symb->getLHS(updatedValues, 0, effSym->effect.size()) || (updatedValues.size() == 0))
          return NULL;
       #if FT_DEBUG_TRANSFORM > 0
	   cout << "[Adjucator-Median-" << this << "] {" ;
	   for(set<SgExpression *>::iterator it2 = updatedValues.begin(); it2 != updatedValues.end(); ++it2)
	       cout << (*it2)->unparseToString() << ", ";
	   cout << "}" << endl;
       #endif
     //Build variable declarations
       stringstream ss;
       ss << "_" << updatedValues.size() << "_" << SageInterface::get_name(baseType);
       SgType *typeOfVar = (useAddr ? SageBuilder::buildPointerType(baseType) : baseType);
       SgBasicBlock *bb = SageBuilder::buildBasicBlock();
       SgVariableDeclaration *vX = SageBuilder::buildVariableDeclaration(
                         		SgName("median_vote_res" + ss.str()),
                         		SageBuilder::buildArrayType( typeOfVar, SageBuilder::buildIntVal(updatedValues.size()) ), 
                         		BInterface::buildArrayInitializer(&updatedValues, useAddr),
                        		bb),
			     *iDecl = SageBuilder::buildVariableDeclaration(SgName("median_vote_i" + ss.str()), SageBuilder::buildIntType(), NULL, bb);
       appendStatement( vX, bb );
       appendStatement( iDecl, bb );

       SgAssignInitializer *initItem = SageBuilder::buildAssignInitializer(
					SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
						SageBuilder::buildVarRefExp(vX),
						SageBuilder::buildVarRefExp(iDecl)), typeOfVar),
			   *initIndex = SageBuilder::buildAssignInitializer(SageBuilder::buildVarRefExp(iDecl), SageBuilder::buildIntType());
       SgVariableDeclaration *itemV = SageBuilder::buildVariableDeclaration(SgName("median_vote_item" + ss.str()), typeOfVar, initItem, bb), 
			     *indexV = SageBuilder::buildVariableDeclaration(SgName("median_vote_index" + ss.str()), SageBuilder::buildIntType(), initIndex, bb);

	this->resVec = vX;	

	/*Default method for median voting:
		1) Sort n elements
		2) Retrieve median element
					    / elem[n/2]   				//if n is odd...
				median = |
					    \ (elem[floor(n/2)] + elem[ceil(n/2)]) / 2 	//... else */
	//Implement algorithm (uses insertion sort).
	  appendStatement( SageBuilder::buildBasicBlock(
			SageBuilder::buildForStatement(
				SageBuilder::buildExprStatement(SageBuilder::buildBinaryExpression<SgAssignOp>(SageBuilder::buildVarRefExp(iDecl), SageBuilder::buildIntVal(1))),
				SageBuilder::buildExprStatement(
					SageBuilder::buildBinaryExpression<SgLessThanOp>(
				     	SageBuilder::buildVarRefExp(iDecl), 
				          SageBuilder::buildIntVal(updatedValues.size()) )),
				SageBuilder::buildPlusPlusOp(SageBuilder::buildVarRefExp(iDecl), SgUnaryOp::postfix),
				SageBuilder::buildBasicBlock(
					itemV,
					indexV,
					SageBuilder::buildWhileStmt(
						SageBuilder::buildExprStatement(
							SageBuilder::buildBinaryExpression<SgAndOp>(
								SageBuilder::buildBinaryExpression<SgGreaterThanOp>(
									SageBuilder::buildVarRefExp(indexV),
									SageBuilder::buildIntVal(0)),
								SageBuilder::buildBinaryExpression<SgGreaterThanOp>(
									SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
				                         	SageBuilder::buildVarRefExp(vX),
				                         	SageBuilder::buildBinaryExpression<SgSubtractOp>(
											SageBuilder::buildVarRefExp(indexV),
											SageBuilder::buildIntVal(1)) ),
									SageBuilder::buildVarRefExp(itemV)) )),
						SageBuilder::buildBasicBlock(
							SageBuilder::buildAssignStatement(
								SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
				                         SageBuilder::buildVarRefExp(vX),
									SageBuilder::buildVarRefExp(indexV)),
								SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
				                         SageBuilder::buildVarRefExp(vX),
				                         SageBuilder::buildBinaryExpression<SgSubtractOp>(
										SageBuilder::buildVarRefExp(indexV),
										SageBuilder::buildIntVal(1)) )),
							SageBuilder::buildAssignStatement(
								SageBuilder::buildVarRefExp(indexV),
								SageBuilder::buildBinaryExpression<SgSubtractOp>(
									SageBuilder::buildVarRefExp(indexV),
									SageBuilder::buildIntVal(1)) ))),
					SageBuilder::buildAssignStatement(
						SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
				               SageBuilder::buildVarRefExp(vX),
							SageBuilder::buildVarRefExp(indexV)),
						SageBuilder::buildVarRefExp(itemV)) ))), bb);
	  
	  medianElement = (updatedValues.size() % 2 == 0 ? 
					//For even sized sets pick mean of elements at (n/2) & (n/2 +1)
					  (SgExpression *) SageBuilder::buildBinaryExpression<SgDivideOp>(
						SageBuilder::buildBinaryExpression<SgAddOp>(
							SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
                        				SageBuilder::buildVarRefExp(vX), SageBuilder::buildIntVal(updatedValues.size()/2)),
							SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
                        				SageBuilder::buildVarRefExp(vX), SageBuilder::buildIntVal(updatedValues.size()/2 + 1))),
						SageBuilder::buildIntVal(2)) :
					//For odd size pick element at floor(n/2)
					  (SgExpression *) SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
						SageBuilder::buildVarRefExp(vX), 
						SageBuilder::buildIntVal(updatedValues.size()/2 + 1)) );
     //Get destination symbol...
       FT::Common::Region_Desc *regDest = declClos->moreSafe(symb->getRegion(), 1);
       FT::Transform::SymbDesc *symDest = dynamic_cast<FT::Transform::SymbDesc *>(regDest->getSymbol());
       ROSE_ASSERT(symDest != NULL);

     appendStatement( SageBuilder::buildAssignStatement(symDest->project(0), medianElement), bb);
     return bb;
}

SgStatement *FT::Transform::Adjucator_Voting_Exact::getHandler(Closure *declClos, FT::Common::EffectVal *effect, ControlStruct *secondCS) {
     //Make sure we're dealing with a symbolic effect...
       SymbDesc *symb = dynamic_cast<SymbDesc *>(effect->s);
       Effect_Symbolic *effSym = dynamic_cast<Effect_Symbolic *>(effect->e);
       if( (symb == NULL) || (effSym == NULL) ) {
	  cout << "(Adjucator_Exact-" << this << ") Ignoring effect " << *effect << endl;
	  return NULL;
       }
     //Initialize
       SgType *baseType = symb->getRegion()->getType();
       bool useAddr = c->adjUseAddrOfVar(baseType);
       set<SgExpression *> updatedValues;
       if(!symb->getLHS(updatedValues, 0, effSym->effect.size()) || (updatedValues.size() == 0))
          return NULL;
	
       SgBasicBlock *bb = SageBuilder::buildBasicBlock();
       SgType *typeOfVar = (useAddr ? SageBuilder::buildPointerType(baseType) : baseType);
       #if FT_DEBUG_TRANSFORM > 0
	   cout << "[Adjucator-Exact-" << this << "] " << (assumeMajElemExist ? "TRUE" : "FALSE") << " {" ;
	   for(set<SgExpression *>::iterator it2 = updatedValues.begin(); it2 != updatedValues.end(); ++it2)
	       cout << (*it2)->unparseToString() << ", ";
	   cout << "}" << endl;
       #endif
     //Decide which algorithm to use...
       if(assumeMajElemExist) {
         /*The following algorithm (from Robert S. Boyer, J Strother Moore, "MJRTY - A Fast Majority Vote Algorithm", 1982),
           finds the majority vote in O(n) if it exists, otherwise the output in undefined/invalid.*/
	     //Declare result vector, index counter, majority counter...
            updatedValues.insert(updatedValues.begin(), SageBuilder::buildCastExp(SageBuilder::buildIntVal(0), typeOfVar, SgCastExp::e_C_style_cast) );
            SgVariableDeclaration *vX = SageBuilder::buildVariableDeclaration(
				         SgName("exact_vote_res_" + SageInterface::get_name(baseType)),
				         SageBuilder::buildArrayType( typeOfVar, SageBuilder::buildIntVal(updatedValues.size()+1) ), 
				         BInterface::buildArrayInitializer(&updatedValues, useAddr),
				         bb),
				  *iDecl = SageBuilder::buildVariableDeclaration(SgName("exact_vote_i"), SageBuilder::buildIntType(), NULL, bb),
				  *cntVoteDecl = SageBuilder::buildVariableDeclaration(SgName("exact_vote_cnt"), SageBuilder::buildIntType(), NULL, bb);
            appendStatement( vX, bb );
	    appendStatement( iDecl, bb );
	    appendStatement( cntVoteDecl, bb );
          //Get destination symbol...
       	    FT::Common::Region_Desc *regDest = declClos->moreSafe(symb->getRegion(), 1);
            FT::Transform::SymbDesc *symDest = dynamic_cast<FT::Transform::SymbDesc *>(regDest->getSymbol());
            ROSE_ASSERT(symDest != NULL);
          //Include for loop...
            appendStatement(
		SageBuilder::buildForStatement(
		     SageBuilder::buildExprStatement(
		          SageBuilder::buildBinaryExpression<SgCommaOpExp>(
		               SageBuilder::buildBinaryExpression<SgAssignOp>(SageBuilder::buildVarRefExp(iDecl), SageBuilder::buildIntVal(1)),
		               SageBuilder::buildBinaryExpression<SgAssignOp>(SageBuilder::buildVarRefExp(cntVoteDecl), SageBuilder::buildIntVal(0)))),
		     SageBuilder::buildExprStatement(
		          SageBuilder::buildBinaryExpression<SgLessThanOp>(
		               SageBuilder::buildVarRefExp(iDecl), 
		               SageBuilder::buildIntVal(updatedValues.size()+1) )),
		     SageBuilder::buildPlusPlusOp(SageBuilder::buildVarRefExp(iDecl), SgUnaryOp::postfix),
		     SageBuilder::buildIfStmt(
		          SageBuilder::buildBinaryExpression<SgEqualityOp>(
		               SageBuilder::buildVarRefExp(cntVoteDecl),
		               SageBuilder::buildIntVal(0)),
		          SageBuilder::buildBasicBlock(
		               SageBuilder::buildAssignStatement(
		                    SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
		                         SageBuilder::buildVarRefExp(vX),
		                         SageBuilder::buildIntVal(0)),
		                    SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
		                         SageBuilder::buildVarRefExp(vX),
		                         SageBuilder::buildVarRefExp(iDecl))),
		               SageBuilder::buildAssignStatement(
		                    SageBuilder::buildVarRefExp(cntVoteDecl),
		                    SageBuilder::buildIntVal(1))),
		          SageBuilder::buildIfStmt(
		               SageBuilder::buildBinaryExpression<SgEqualityOp>(
		                    SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
		                         SageBuilder::buildVarRefExp(vX),
		                         SageBuilder::buildIntVal(0)),
		                    SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
		                         SageBuilder::buildVarRefExp(vX),
		                         SageBuilder::buildVarRefExp(iDecl))),
		               SageBuilder::buildExprStatement(SageBuilder::buildPlusPlusOp(SageBuilder::buildVarRefExp(cntVoteDecl), SgUnaryOp::postfix)),
		               SageBuilder::buildExprStatement(SageBuilder::buildMinusMinusOp(SageBuilder::buildVarRefExp(cntVoteDecl), SgUnaryOp::postfix)) ))), bb);
	    appendStatement(
		SageBuilder::buildAssignStatement(
			symDest->project(0),
			SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(
		     		SageBuilder::buildVarRefExp(vX),
			        SageBuilder::buildIntVal(0))), bb);
       } else {
		/*Default method for exact majority voting:
			1) Retrieve min, max and median element (by median voting)
			2) Majority vote on the median elem. iif (median == min) OR (median == max)*/
		Adjucator_Voting_Median medianVoter(this->c);
		SgBasicBlock *bbMedian = static_cast<SgBasicBlock *>(medianVoter.getHandler(declClos, effect, secondCS));
		ROSE_ASSERT((bbMedian != NULL) && (medianVoter.medianElement != NULL) && (medianVoter.resVec != NULL));
		SgStatement *medianAssign = bbMedian->get_statements().at(bbMedian->get_statements().size()-1);
		SageInterface::removeStatement(medianAssign);
		//Invoke second-level FP...
		  SgStatement *secFPStm = NULL;
		  if(secondCS != NULL) {
			vector<FT::Common::EffectVal *> tmpVec;
			tmpVec.push_back(effect);
			secFPStm = secondCS->getHandler(declClos, tmpVec);
		  }
		//Create implementation...
		  appendStatement(bbMedian, bb);
		  appendStatement(
			SageBuilder::buildIfStmt(
				SageBuilder::buildBinaryExpression<SgOrOp>(
					SageBuilder::buildBinaryExpression<SgEqualityOp>(
						SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(	//min element
							SageBuilder::buildVarRefExp(medianVoter.resVec),
							SageBuilder::buildIntVal(0)),
						SageInterface::copyExpression(medianVoter.medianElement) ),
					SageBuilder::buildBinaryExpression<SgEqualityOp>(
						SageBuilder::buildBinaryExpression<SgPntrArrRefExp>(	//max element
							SageBuilder::buildVarRefExp(medianVoter.resVec),
							SageBuilder::buildIntVal(updatedValues.size()-1)),
						SageInterface::copyExpression(medianVoter.medianElement) ) ),
				medianAssign, 
				secFPStm), bb);
		
	  }
	return bb;							
}

