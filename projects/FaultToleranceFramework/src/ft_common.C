#include <sstream>
#include <string>
#include <iostream>

#include "rose.h"
#include "ft_common.h"

using namespace std;

///////////////////////////////////////// Misc. functions /////////////////////////////////////////
string FT::Common::toString(FT::Common::SymbDesc *desc) {
	stringstream ss;
	ss << *desc;
	return ss.str();
}

/////////////////////////////////////////// Singleton /////////////////////////////////////////////
string FT::Common::Singleton::getRegionName(Region_Desc *r) {
	ROSE_ASSERT(r != NULL);
	string name;
	if(r->getName() == "") {			
	   stringstream ss;		
	   //Assign name based on parent relationship...
	     if(r->getParent() != NULL) {
		name = getRegionName(r->getParent());
		ss << "-$" << r->getParent()->nrSubRegions();
	     } else {
		ss << regionCnt;
		regionCnt++;
	     }
	   //Complete name...
	     name = name + ss.str();
	} else
		name = r->getName();					
	return name;
}

/////////////////////////////////////// Region descriptor ///////////////////////////////////////
FT::Common::Region_Desc::Region_Desc(SymbDesc *sym, Region_Desc *parent, SgType *type, SgName name) {
	ROSE_ASSERT(parent != NULL);
	//Initialize state...
	  this->type = NULL;
	  this->sym = sym;
	  this->parent = parent;
	  this->regionName = name;
	  this->type = (type == NULL ? parent->getType() : type);
	//Set name (if neccessary)
	  this->regionName = Singleton::getInstance().getRegionName(this);
}
FT::Common::Region_Desc::Region_Desc(SymbDesc *sym, SgType *type, SgName name) {
	ROSE_ASSERT(type != NULL);
	//Initialize state...
	  this->type = type;
	  this->sym = sym;
	  this->parent = NULL;
	  this->regionName = name;
	//Set name (if neccessary)
	  this->regionName = Singleton::getInstance().getRegionName(this);
}

FT::Common::Region_Desc::~Region_Desc() {

}

void FT::Common::Region_Desc::print(ostream &o) const {
	o << "<(Region) '" << regionName << "' ";
	if(parent != NULL)
		o << *parent << " ";
	else
		o << "<NULL> ";
	if(type != NULL)
		o << "'" << type->unparseToString() << "' {";
	else
		o << "NULL {";
	for(map<SgName, Region_Desc *>::const_iterator it = subRegions.begin();
	    it != subRegions.end();
	    ++it)
		o << it->first << "=(" << it->second << "), ";	
	o << "}>";
}

void FT::Common::Region_Desc::getRegionNames(set<SgName> &setRName) {
	for(map<SgName, Region_Desc *>::iterator it = subRegions.begin();
	    it != subRegions.end();
	    ++it)
		setRName.insert(it->first);
}

FT::Common::Region_Desc *FT::Common::Region_Desc::getRegion(SgName n) {
	map<SgName, Region_Desc *>::iterator it = subRegions.find(n);
	if(it == subRegions.end())
	   return NULL;
	else
	   return it->second;
}

FT::Common::Region_Desc *FT::Common::Region_Desc::addRegion(SgName name, Region_Desc *r) {
	//Check for alias...
	  for(map<SgName, Region_Desc *>::iterator it = subRegions.begin(); it != subRegions.end(); ++it) {
	      //Only look for named regions
		if(it->second->hasSymbol()) {
		      SymbDesc *sym = it->second->getSymbol();
		      if(sym->hasAlias(name) != NULL) {
			  sym->addAlias(this->getSymbol());
			  this->getSymbol()->addAlias(sym);
			  return r;
		      }
	        }
	  }
	//Add it and return
	  subRegions[name] = r;
	return r;
}

FT::Common::SymbDesc *FT::Common::Region_Desc::getSymbol() {
	//Check if a symbol already has been assigned...
	  if(this->sym != NULL)
	     return this->sym;
	//Create a symbol...
	  this->sym = new SymbTerm(getName(), 1, this);

	return this->sym;
}

///////////////////////////////////////// Symbol /////////////////////////////////////////
FT::Common::SymbDesc::SymbDesc(SYM_TYPE sT, SgName name, Region_Desc *rD, SgType *type) {
	this->sT = sT;
	this->parentSymb = NULL;
	if(rD == NULL)
		this->rD = new Region_Desc(this, type, name);
	else
		this->rD = rD;
}
void FT::Common::SymbDesc::print(ostream &o) const {
	o << "(SymbDesc-" << this << ") " << sT << " " << *rD << " <";
	if(parentSymb != NULL)
	   o << *parentSymb ;
	o << ">, {";
	for(set<SymbDesc *>::iterator it = aliasSym.begin(); it != aliasSym.end(); ++it)
	    o << *it << ", ";
	o << "}";
}
FT::Common::SymbDesc *FT::Common::SymbDesc::addAlias(SymbDesc *desc) {
	aliasSym.insert(desc);
	return desc;
}
FT::Common::SymbDesc *FT::Common::SymbDesc::hasAlias(SgName n) {
	//TODO! This function has to be updated as more sophisticated naming schemes are
	//implemented.

	//Make sure name doesn't alias any other...
	#ifdef FT_ASSUME_OPTIMISTIC_ALIASING
	  #ifdef FT_POST_WARNING_MSG_ON_SCREEN
	   	cout << "WARNING! Current assumption allows two symbols to be "
			"non-overlapping unless names are equal. See FT_ASSUME_OPTIMISTIC_ALIASING" << endl;
	  #endif
	  for(set<SymbDesc *>::iterator it = aliasSym.begin(); it != aliasSym.end(); ++it)
	      if( (*it)->getName() == n)
		  return *it;
	  return NULL;
	#else
	  for(set<SymbDesc *>::iterator it = aliasSym.begin(); it != aliasSym.end(); ++it)
	      if(it->first == n)
		 return *it;
	  ROSE_ASSERT(false);
	#endif
}




void FT::Common::SymbTerm::print(ostream &o) const {
	o << "(SymbTerm-" << this << ") " << N << " " << name << " ";
	o << "<";
		SymbDesc::print(o);
	o << ", <" << *getRegion() << ">>";
}




SgName FT::Common::SymbNonTerm::getName() {
	string s = getExp()->unparseToString();
	struct Visitor : public AstSimpleProcessing {
		string &s;
		Visitor(string &s_) : s(s_) {}
		virtual void visit(SgNode *n) {
			//Only apply op for expressions
			  SgExpression *exp = isSgExpression(n);
			  if(exp == NULL)
			     return;
			//Has sub-expression been named?
			  if(!TInterface::hasValueAttribute(exp, FT_TRANFORMATION_NODE_ATTR "VAR"))
			     return;
			  FT::Common::Region_Desc *r = TInterface::GetValueAttribute<FT::Common::Region_Desc *>(exp, FT_TRANFORMATION_NODE_ATTR "VAR");
			//Replace sub-expression string with name
			  boost::replace_all(s, exp->unparseToString(), r->getName().getString());				  
		}
		void atTraversalEnd() {}	
	} expTransformer(s);
	expTransformer.traverse(getExp(), preorder);
	return SgName(s);
}
void FT::Common::SymbNonTerm::print(ostream &o) const {
	o << "(SymbNonTerm-" << this << ") '" << exp->unparseToString() << "'";
	o << " <";
		SymbDesc::print(o);
	o << "> {";
	for(set<SymbDesc *>::const_iterator it = symbols.begin(); it != symbols.end(); ++it)
	    o << *it << ", ";
	o << "}";
}
