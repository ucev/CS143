#ifndef SEMANT_H_
#define SEMANT_H_

#include <assert.h>
#include <iostream>
#include <map>
#include <set>
#include <vector>
#include "cool-tree.h"
#include "stringtab.h"
#include "symtab.h"
#include "list.h"

#define TRUE 1
#define FALSE 0

using namespace std;

class ClassTable;
typedef ClassTable *ClassTableP;

// This is a structure that may be used to contain the semantic
// information such as the inheritance graph.  You may use it or not as
// you like: it is only here to provide a container for the supplied
// methods.

class ClassTable {
private:
  int semant_errors;

  map<Symbol, class__class*> class_map;
  set<Symbol> basic_class_set;
  map<Symbol, set<Symbol> > inherit_graph;
  map<Symbol, map<Symbol, method_class*> > method_map;

  void install_basic_classes();
  void install_user_classes(Classes);
  void install_method_map();
  void verify_signature(class__class*, method_class*);

  int check_circle();
  int check_class_circle(class__class*, map<Symbol, int> & depth_map);

  ostream& error_stream;

public:
  ClassTable(Classes);
  int errors() { return semant_errors; }
  ostream& semant_error();
  ostream& semant_error(Class_ c);
  ostream& semant_error(Symbol filename, tree_node *t);

  void fatal();

  class__class * get_parent(Symbol);
  bool class_exists(Symbol);
  bool is_child(Symbol, Symbol);
  bool method_exists(Symbol, Symbol);
  vector<Symbol> get_signatures(Symbol, Symbol);
  method_class *get_method(Symbol, Symbol);
  Symbol least_upper_bound(Symbol, Symbol);
};


#endif

