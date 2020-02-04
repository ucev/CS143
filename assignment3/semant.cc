

#include <stdlib.h>
#include <stdio.h>
#include <stdarg.h>
#include "semant.h"
#include "utilities.h"
#include "typeinfo"

#include <queue>
#include <vector>


extern int semant_debug;
extern char *curr_filename;

//////////////////////////////////////////////////////////////////////
//
// Symbols
//
// For convenience, a large number of symbols are predefined here.
// These symbols include the primitive type and method names, as well
// as fixed names used by the runtime system.
//
//////////////////////////////////////////////////////////////////////
static Symbol 
    arg,
    arg2,
    Bool,
    concat,
    cool_abort,
    copy_s,
    Int,
    in_int,
    in_string,
    IO,
    length,
    Main,
    main_meth,
    No_class,
    No_type,
    Object,
    out_int,
    out_string,
    prim_slot,
    self,
    SELF_TYPE,
    Str,
    str_field,
    substr,
    type_name,
    val;
//
// Initializing the predefined symbols.
//
static void initialize_constants(void)
{
    arg         = idtable.add_string("arg");
    arg2        = idtable.add_string("arg2");
    Bool        = idtable.add_string("Bool");
    concat      = idtable.add_string("concat");
    cool_abort  = idtable.add_string("abort");
    copy_s      = idtable.add_string("copy");
    Int         = idtable.add_string("Int");
    in_int      = idtable.add_string("in_int");
    in_string   = idtable.add_string("in_string");
    IO          = idtable.add_string("IO");
    length      = idtable.add_string("length");
    Main        = idtable.add_string("Main");
    main_meth   = idtable.add_string("main");
    //   _no_class is a symbol that can't be the name of any 
    //   user-defined class.
    No_class    = idtable.add_string("_no_class");
    No_type     = idtable.add_string("_no_type");
    Object      = idtable.add_string("Object");
    out_int     = idtable.add_string("out_int");
    out_string  = idtable.add_string("out_string");
    prim_slot   = idtable.add_string("_prim_slot");
    self        = idtable.add_string("self");
    SELF_TYPE   = idtable.add_string("SELF_TYPE");
    Str         = idtable.add_string("String");
    str_field   = idtable.add_string("_str_field");
    substr      = idtable.add_string("substr");
    type_name   = idtable.add_string("type_name");
    val         = idtable.add_string("_val");
}

Symbol formatSelfType(Symbol type1, Symbol type2) {
    return type1 == SELF_TYPE ? type2 : type1;
}

ClassTable::ClassTable(Classes classes) : semant_errors(0) , error_stream(cerr) {

    /* Fill this in */
    install_basic_classes();
    install_user_classes(classes);
    int has_circle = check_circle();
    if (has_circle) {
        semant_error() << "Circle found in inheritance graph." << endl;
        fatal();
    }
    install_method_map();
}

void ClassTable::install_basic_classes() {

    // The tree package uses these globals to annotate the classes built below.
   // curr_lineno  = 0;
    Symbol filename = stringtable.add_string("<basic class>");
    
    // The following demonstrates how to create dummy parse trees to
    // refer to basic Cool classes.  There's no need for method
    // bodies -- these are already built into the runtime system.
    
    // IMPORTANT: The results of the following expressions are
    // stored in local variables.  You will want to do something
    // with those variables at the end of this method to make this
    // code meaningful.

    // 
    // The Object class has no parent class. Its methods are
    //        abort() : Object    aborts the program
    //        type_name() : Str   returns a string representation of class name
    //        copy() : SELF_TYPE  returns a copy of the object
    //
    // There is no need for method bodies in the basic classes---these
    // are already built in to the runtime system.

    Class_ Object_class =
	class_(Object, 
	       No_class,
	       append_Features(
			       append_Features(
					       single_Features(method(cool_abort, nil_Formals(), Object, no_expr())),
					       single_Features(method(type_name, nil_Formals(), Str, no_expr()))),
			       single_Features(method(copy_s, nil_Formals(), SELF_TYPE, no_expr()))),
	       filename);

    // 
    // The IO class inherits from Object. Its methods are
    //        out_string(Str) : SELF_TYPE       writes a string to the output
    //        out_int(Int) : SELF_TYPE            "    an int    "  "     "
    //        in_string() : Str                 reads a string from the input
    //        in_int() : Int                      "   an int     "  "     "
    //
    Class_ IO_class = 
	class_(IO, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       single_Features(method(out_string, single_Formals(formal(arg, Str)),
										      SELF_TYPE, no_expr())),
							       single_Features(method(out_int, single_Formals(formal(arg, Int)),
										      SELF_TYPE, no_expr()))),
					       single_Features(method(in_string, nil_Formals(), Str, no_expr()))),
			       single_Features(method(in_int, nil_Formals(), Int, no_expr()))),
	       filename);

    //
    // The Int class has no methods and only a single attribute, the
    // "val" for the integer. 
    //
    Class_ Int_class =
	class_(Int, 
	       Object,
	       single_Features(attr(val, prim_slot, no_expr())),
	       filename);

    //
    // Bool also has only the "val" slot.
    //
    Class_ Bool_class =
	class_(Bool, Object, single_Features(attr(val, prim_slot, no_expr())),filename);

    //
    // The class Str has a number of slots and operations:
    //       val                                  the length of the string
    //       str_field                            the string itself
    //       length() : Int                       returns length of the string
    //       concat(arg: Str) : Str               performs string concatenation
    //       substr(arg: Int, arg2: Int): Str     substring selection
    //       
    Class_ Str_class =
	class_(Str, 
	       Object,
	       append_Features(
			       append_Features(
					       append_Features(
							       append_Features(
									       single_Features(attr(val, Int, no_expr())),
									       single_Features(attr(str_field, prim_slot, no_expr()))),
							       single_Features(method(length, nil_Formals(), Int, no_expr()))),
					       single_Features(method(concat, 
								      single_Formals(formal(arg, Str)),
								      Str, 
								      no_expr()))),
			       single_Features(method(substr, 
						      append_Formals(single_Formals(formal(arg, Int)), 
								     single_Formals(formal(arg2, Int))),
						      Str, 
						      no_expr()))),
	       filename);
    
    basic_class_set.insert(Object);
    basic_class_set.insert(IO);
    basic_class_set.insert(Int);
    basic_class_set.insert(Bool);
    basic_class_set.insert(Str);
    basic_class_set.insert(SELF_TYPE);

    class_map.insert(make_pair(Object, (class__class*)Object_class));
    class_map.insert(make_pair(IO, (class__class*)IO_class));
    class_map.insert(make_pair(Int, (class__class*)Int_class));
    class_map.insert(make_pair(Bool, (class__class*)Bool_class));
    class_map.insert(make_pair(Str, (class__class*)Str_class));

    inherit_graph[No_class].insert(Object);
    inherit_graph[Object].insert(IO);
    inherit_graph[Object].insert(Int);
    inherit_graph[Object].insert(Bool);
    inherit_graph[Object].insert(Str);
}

void ClassTable::install_user_classes(Classes classes)
{
    int hasMainClass = FALSE;
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        class__class *cls = (class__class*)classes->nth(i);
        if (class_map.count(cls->get_name())) {
            semant_error(cls->get_filename(), cls) << "Class " << cls->get_name() << " was previously defined." << endl;
            fatal();
        }

        if (basic_class_set.count(cls->get_name())) {
            semant_error(cls->get_filename(), cls) << "Redefinition of basic class " << cls->get_name() << endl;
            fatal();
        }

        if (cls->get_name() == Main) {
            hasMainClass = true;
        }

        class_map.insert(make_pair(cls->get_name(), cls));
    }

    if (!hasMainClass) {
        semant_error() << "Class Main is not defined." << endl;
        fatal();
    }

    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        class__class *cls = (class__class*)classes->nth(i);
        Symbol parent = cls->get_parent();

        if (parent == Int || parent == Bool || parent == Str) {
            semant_error(cls->get_filename(), cls) << "Class " << cls->get_name() << " can't inherit class " << parent << endl;
            fatal();
        }

        if (parent == SELF_TYPE) {
            semant_error(cls->get_filename(), cls) << "Class " << cls->get_name() << " can't inherit SELF_TYPE." << endl;
            fatal();
        }

        if (!class_map.count(parent)) {
            semant_error(cls->get_filename(), cls) << "Class " << cls->get_name() << " can't inherit no-existing class." << endl;
            fatal();
        }

        inherit_graph[parent].insert(cls->get_name());
    }
}

int ClassTable::check_circle()
{
    map<Symbol, int> depth_map;
    class__class *object_class = class_map[Object];
    depth_map.insert(make_pair(Object, 0));
    return check_class_circle(object_class, depth_map);
}

int ClassTable::check_class_circle(class__class *cls, map<Symbol, int> & depth_map)
{
    int depth = depth_map.find(cls->get_name())->second;
    set<Symbol> children_list = inherit_graph[cls->get_name()];
    set<Symbol>::iterator iter;
    for (iter = children_list.begin(); iter != children_list.end(); ++iter) {
        Symbol s = *iter;
        if (depth_map.count(s) != 0) {
            return TRUE;
        }
        depth_map.insert(make_pair(s, depth + 1));
        if (check_class_circle(class_map[s], depth_map)) {
            return TRUE;
        }
    }
    return FALSE;
}

void ClassTable::install_method_map()
{
    bool has_main_method = false;
    bool main_has_formals = false;
    queue<Symbol> q;
    q.push(Object);
    
    Symbol c;
    while (!q.empty()) {
        c = q.front();
        q.pop();
        class__class *cls = class_map[c];
        Features features = cls->get_features();
        for (int i = features->first(); features->more(i); i = features->next(i)) {
            Feature feature = (Feature) features->nth(i);
            if (feature->get_is_method()) {
                method_class *method = (method_class*)feature;
                verify_signature(cls, method);
                method_map[c][method->get_name()] = method;
                if (c == Main && method->get_name() == main_meth) {
                    has_main_method = true;
                    Formals formals = method->get_formals();
                    if (formals->len() > 0) {
                        main_has_formals = true;
                    }
                }
            }
        }

        map<Symbol, method_class*> parent_methods = method_map[cls->get_parent()];
        map<Symbol, method_class*>::iterator iter;
        for (iter = parent_methods.begin(); iter != parent_methods.end(); ++iter) {
            // overload
            if (method_map[c].count(iter->first) == 0) {
                method_map[c][iter->first] = iter->second;
            }
        }

        set<Symbol> child_list = inherit_graph[c];
        set<Symbol>::iterator child_iter;
        for (child_iter = child_list.begin(); child_iter != child_list.end(); ++child_iter) {
            q.push(*child_iter);
        }
    }

    if (!has_main_method) {
        semant_error(class_map[c]->get_filename(), class_map[c]) << "No main method found." << endl;
    }
    if (main_has_formals) {
        semant_error(class_map[c]->get_filename(), class_map[c]) << "main method shouldn't have formals." << endl;
    }
}

void ClassTable::verify_signature(class__class *cls, method_class* method)
{
    Formals formals = method->get_formals();
    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        formal_class *formal = (formal_class*)formals->nth(i);
        if (formal->get_name() == self) {
            semant_error(cls->get_filename(), cls) << "formal list shouldn't have self." << endl;
        }
        if (formal->get_name() == SELF_TYPE) {
            semant_error(cls->get_filename(), cls) << "formal list shouldn't has SELF_TYPE." << endl;
        }

        // add
        // if (class_map[formal->get_type_decl()] == NULL) {
        //     semant_error(cls->get_filename(), cls) << "formal type not defined in method." << endl;
        // }
    }

    if (method->get_return_type() != SELF_TYPE && class_map[method->get_return_type()] == NULL) {
        semant_error(cls->get_filename(), cls) << "return type not defined in method." << endl;
    }
}

class__class * ClassTable::get_parent(Symbol name)
{
    class__class *cls = class_map[name];
    return class_map[cls->get_parent()];
}

bool ClassTable::class_exists(Symbol name)
{
    return class_map.count(name) > 0;
}

/**
 * 不能传 SELF_TYPE，调用时已经做了处理
 */
bool ClassTable::is_child(Symbol c1, Symbol c2)
{
    class__class *cls = class_map[c1];
    while (cls && cls->get_name() != c2) {
        cls = class_map[cls->get_parent()];
    }
    return cls && cls->get_name() == c2;
}

bool ClassTable::method_exists(Symbol class_name, Symbol method_name)
{
    if (method_map.count(class_name) != 0) {
        map<Symbol, method_class*> methods = method_map[class_name];
        return methods.count(method_name) != 0;
    }
    return false;
}

method_class * ClassTable::get_method(Symbol class_name, Symbol method_name)
{
    if (method_exists(class_name, method_name)) {
        return method_map[class_name][method_name];
    }
    return NULL;
}

vector<Symbol> ClassTable::get_signatures(Symbol class_name, Symbol method_name)
{
    vector<Symbol> sig;
    method_class *method = get_method(class_name, method_name);
    if (method) {
        Formals formals = method->get_formals();
        for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
            formal_class *f = (formal_class*)formals->nth(i);
            sig.push_back(f->get_type_decl());
        }
        sig.push_back(method->get_return_type());
    }
    return sig;
}

Symbol ClassTable::least_upper_bound(Symbol c1, Symbol c2)
{
    set<Symbol> parents;
    Symbol s = c1;
    while (s != No_class) {
        parents.insert(s);
        s = class_map[s]->get_parent();
    }
    s = c2;
    while (s != No_class && parents.find(s) == parents.end()) {
        s = class_map[s]->get_parent();
    }
    return s == No_class ? Object : s;
}


////////////////////////////////////////////////////////////////////
//
// semant_error is an overloaded function for reporting errors
// during semantic analysis.  There are three versions:
//
//    ostream& ClassTable::semant_error()                
//
//    ostream& ClassTable::semant_error(Class_ c)
//       print line number and filename for `c'
//
//    ostream& ClassTable::semant_error(Symbol filename, tree_node *t)  
//       print a line number and filename
//
///////////////////////////////////////////////////////////////////

ostream& ClassTable::semant_error(Class_ c)
{                                                             
    return semant_error(c->get_filename(),c);
}    

ostream& ClassTable::semant_error(Symbol filename, tree_node *t)
{
    error_stream << filename << ":" << t->get_line_number() << ": ";
    return semant_error();
}

ostream& ClassTable::semant_error()                  
{                                                 
    semant_errors++;                            
    return error_stream;
}

void ClassTable::fatal() {
  cerr<<"Compilation halted due to static semantic errors."<<endl;
  exit(1);
}


/*   This is the entry point to the semantic checker.

     Your checker should do the following two things:

     1) Check that the program is semantically correct
     2) Decorate the abstract syntax tree with type information
        by setting the `type' field in each Expression node.
        (see `tree.h')

     You are free to first do 1), make sure you catch all semantic
     errors. Part 2) can be done in a second stage, when you want
     to build mycoolc.
 */
void program_class::semant()
{
    initialize_constants();

    /* ClassTable constructor may do some semantic analysis */
    ClassTable *classtable = new ClassTable(classes);

    /* some semantic analysis code may go here */
    OcurredExpection = false;
    sv = new semanVisitor(classtable);

    this->accept(sv);

    if (classtable->errors()) {
	cerr << "Compilation halted due to static semantic errors." << endl;
	exit(1);
    }
}

void semanVisitor::visit(Program e)
{
	cerr << "public void visit (Program e) should never be called." << endl;
}

void semanVisitor::visit(Class_ e)
{
    cerr << "public void visit (Class_ e) should never be called." << endl;
}

void semanVisitor::visit(Feature e)
{
    cerr << "public void visit (Feature e) should never be called." << endl;
}

void semanVisitor::visit(Formal e)
{
    cerr << "public void visit (Formal e) should never be called." << endl;
}

void semanVisitor::visit(Case e)
{
    cerr << "public void visit (Case e) should never be called." << endl;
}

void semanVisitor::visit(Expression e)
{
    // if (typeid(*e) == typeid(branch_class)) {
    //     visit((branch_class*) e);
    // } else 
    if (typeid(*e) == typeid(assign_class)) {
        visit((assign_class*) e);
    } else if (typeid(*e) == typeid(static_dispatch_class)) {
        visit((static_dispatch_class*) e);
    } else if (typeid(*e) == typeid(dispatch_class)) {
        visit((dispatch_class*) e);
    } else if (typeid(*e) == typeid(cond_class)) {
        visit((cond_class*) e);
    } else if (typeid(*e) == typeid(loop_class)) {
        visit((loop_class*) e);
    } else if (typeid(*e) == typeid(typcase_class)) {
        visit((typcase_class*) e);
    } else if (typeid(*e) == typeid(block_class)) {
        visit((block_class*) e);
    } else if (typeid(*e) == typeid(let_class)) {
        visit((let_class*) e);
    } else if (typeid(*e) == typeid(plus_class)) {
        visit((plus_class*) e);
    } else if (typeid(*e) == typeid(sub_class)) {
        visit((sub_class*) e);
    } else if (typeid(*e) == typeid(mul_class)) {
        visit((mul_class*) e);
    } else if (typeid(*e) == typeid(divide_class)) {
        visit((divide_class*) e);
    } else if (typeid(*e) == typeid(neg_class)) {
        visit((neg_class*) e);
    } else if (typeid(*e) == typeid(lt_class)) {
        visit((lt_class*) e);
    } else if (typeid(*e) == typeid(eq_class)) {
        visit((eq_class*) e);
    } else if (typeid(*e) == typeid(leq_class)) {
        visit((leq_class*) e);
    } else if (typeid(*e) == typeid(comp_class)) {
        visit((comp_class*) e);
    } else if (typeid(*e) == typeid(int_const_class)) {
        visit((int_const_class*) e);
    } else if (typeid(*e) == typeid(bool_const_class)) {
        visit((bool_const_class*) e);
    } else if (typeid(*e) == typeid(string_const_class)) {
        visit((string_const_class*) e);
    } else if (typeid(*e) == typeid(new__class)) {
        visit((new__class*) e);
    } else if (typeid(*e) == typeid(isvoid_class)) {
        visit((isvoid_class*) e);
    } else if (typeid(*e) == typeid(no_expr_class)) {
        visit((no_expr_class*) e);
    } else if (typeid(*e) == typeid(object_class)) {
        visit((object_class*) e);
    }
}

void semanVisitor::visit(program_class *e)
{
}

void semanVisitor::visit(class__class *e)
{
    currentClass = e;
    Features features = e->get_features();
    Features parent_feature_list = e->parent_feature_list;

    for (int i = features->first(); features->more(i); i = features->next(i)) {
        Feature f1 = (Feature) features->nth(i);
        bool conflictWithParent = false;
        for (int j = parent_feature_list->first(); parent_feature_list->more(j); j = parent_feature_list->next(j)) {
            Feature f2 = (Feature) parent_feature_list->nth(j);
            if (!(f1->get_is_method()) && !(f2->get_is_method())
                && (((attr_class*)f1)->get_name() == ((attr_class*)f2)->get_name())) {
                conflictWithParent = true;
                classTable->semant_error(e->get_filename(), f1) << "attribute " << ((attr_class*)f1)->get_name() << " is an attribute of inherited class." << endl;
                break;
            } else if (f1->get_is_method() && f2->get_is_method()
                && (((method_class*)f1)->get_name() == ((method_class*)f2)->get_name())) {
                method_class *m1 = (method_class*) f1;
                method_class *m2 = (method_class*) f2;
                if (m1->get_return_type() != m2->get_return_type()) {
                    conflictWithParent = true;
                    classTable->semant_error(e->get_filename(), m1) << "return type is different from inherited type." << endl;
                    break;
                }

                Formals formals1 = m1->get_formals();
                Formals formals2 = m2->get_formals();
                if (formals1->len() != formals2->len()) {
                    conflictWithParent = true;
                    classTable->semant_error(e->get_filename(), m1) << "differrent number of formals from parent." << endl;
                    break;
                }

                for (int k = formals1->first(); formals1->more(k); k = formals1->next(k)) {
                    formal_class *fm1 = (formal_class*) formals1->nth(k);
                    formal_class *fm2 = (formal_class*) formals2->nth(k);
                    if (fm1->get_type_decl() != fm2->get_type_decl()) {
                        conflictWithParent = true;
                        classTable->semant_error(e->get_filename(), f1) << "method parameter type is different from parent." << endl;
                        break;
                    }
                }
                // add
                // if (conflictWithParent) {
                //     break;
                // }
            }
        }
        if (!conflictWithParent) {
            for (int k = 0; k < i; k++) {
                Feature f3 = (Feature) features->nth(k);
                if (!(f1->get_is_method()) && !(f3->get_is_method()) && (((attr_class*)f1)->get_name() == ((attr_class*)f3)->get_name())) {
                    classTable->semant_error(e->get_filename(), f1) << "attribute is multi-defined." << endl;
                    break;
                } else if (f1->get_is_method() && f3->get_is_method() && (((method_class*)f1)->get_name() == ((method_class*)f3)->get_name())) {
                    classTable->semant_error(e->get_filename(), f1) << "method is multi-defined." << endl;
                    break;
                }
            }
        }
    }
}

void semanVisitor::visit(method_class *e)
{
    Formals formals = e->get_formals();
    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        formal_class *formal = (formal_class*)formals->nth(i);
        tree_node *t = probeObject(formal->get_name());
        if (t != NULL) {
            if (typeid(*t) == typeid(formal_class)) {
                classTable->semant_error(currentClass->get_filename(), formal)
                    << "formal multi-defiend." << endl;
            }
        } else {
            addId(formal->get_name(), formal, false);
        }
    }

    this->visit(e->get_expr());

    Symbol return_from_method = e->get_return_type();
    Symbol return_from_expr = e->get_expr()->get_type();
    Symbol return_from_method_infer = formatSelfType(return_from_method, currentClass->get_name());
    Symbol return_from_expr_infer = formatSelfType(return_from_expr, currentClass->get_name());

    bool case1 = return_from_method == SELF_TYPE && return_from_expr != SELF_TYPE;
    bool case2 = return_from_method != SELF_TYPE
        && !classTable->is_child(return_from_expr_infer, return_from_method_infer);
    if (case1 || case2) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "return type doesnot match." << endl;
    }
}

void semanVisitor::visit(attr_class *e)
{
    if (e->get_name() == self) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "cannot use 'self' as attribute name." << endl;
    }

    if (e->get_type_decl() != SELF_TYPE && !classTable->class_exists(e->get_type_decl())) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Class " << e->get_type_decl()
            << " of attribute " << e->get_name()
            << " is not defined." << endl;
    }

    visit(e->get_init());

    if (e->get_init()->get_type() == NULL) {
        return;
    }

    Symbol type_decl = e->get_type_decl();
    Symbol type_init = e->get_init()->get_type();
    Symbol type_decl_infer = formatSelfType(type_decl, currentClass->get_name());
    Symbol type_init_infer = formatSelfType(type_init, currentClass->get_name());

    if (!classTable->is_child(type_init_infer, type_decl_infer)) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Initialized type " << type_init
            << " of attribute " << e->get_name()
            << " doesnot conform to the declared type " << type_decl << endl;
    }
}

void semanVisitor::visit(formal_class *e)
{
    if (e->get_type_decl() == SELF_TYPE) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Formals cannot have SELF_TYPE." << endl;
    } else if (!classTable->class_exists(e->get_type_decl())) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Class " << e->get_type_decl()
            << " of formal " << e->get_name()
            << " is not defined." << endl;
    }
}

void semanVisitor::visit(branch_class *e)
{
    addId(e->get_name(), e, false);
    if (!classTable->class_exists(e->get_type_decl())) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Class " << e->get_type_decl()
            << " in case branch is undefined." << endl;
        // e->set_type(Object);
        // return;
    }
    if (e->get_type_decl() == SELF_TYPE) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Identifier " << e->get_name()
            << " declared with SELF_TYPE in case branch." << endl;
    }
    visit(e->get_expr());
}

void semanVisitor::visit(assign_class *e)
{
    Symbol name = e->get_name();
    tree_node *t = lookupObject(name);
    if (t == NULL) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Assigned variable " << name << "is undefined." << endl;
        e->set_type(Object);
        return;
    }
    if (name == self) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "'self' cannot be assigned." << endl;
        e->set_type(Object);
        return;
    }
    Symbol type1 = NULL;
    if (typeid(*t) == typeid(attr_class)) {
        type1 = ((attr_class*)t)->get_type_decl();
    } else if (typeid(*t) == typeid(formal_class)) {
        type1 = ((formal_class*)t)->get_type_decl();
    } else if (typeid(*t) == typeid(branch_class)) {
        type1 = ((branch_class*)t)->get_type_decl();
    } else if (typeid(*t) == typeid(let_class)) {
        type1 = ((let_class*)t)->get_type_decl();
    }

    visit(e->get_expr());
    Symbol type2 = e->get_expr()->get_type();

    Symbol type1_infer = formatSelfType(type1, currentClass->get_name());
    Symbol type2_infer = formatSelfType(type2, currentClass->get_name());

    if (!classTable->is_child(type2_infer, type1_infer)) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "type of assign expression is " << type2_infer
            << ", which doesnot conform to the declared type "
            << type1_infer << " of " << name << endl;
        e->set_type(Object);
        return;
    }
    e->set_type(type2);
}

void semanVisitor::visit(static_dispatch_class *e)
{
    visit(e->get_expr());
    Expressions actual = e->get_actual();
    for (int i = actual->first(); actual->more(i); i = actual->next(i)) {
        visit((Expression_class*)actual->nth(i));
    }

    Symbol static_type = e->get_type_name();
    Symbol static_type_infer = formatSelfType(static_type, currentClass->get_name());

    if (!classTable->method_exists(static_type, e->get_name())) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Cannot dispatch to undefined method." << e->get_name() << endl;
        e->set_type(Object);
        return;
    }

    Symbol type_caller = e->get_expr()->get_type();
    Symbol type_caller_infer = formatSelfType(type_caller, currentClass->get_name());

    if (!classTable->is_child(type_caller_infer, static_type_infer)) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Expression type is " << type_caller_infer
            << ", which doesnot conform to the declared type "
            << static_type << "." << endl;
        e->set_type(Object);
        return;
    }

    vector<Symbol> signatures = classTable->get_signatures(static_type, e->get_name());

    if ((signed)signatures.size() - 1 != actual->len()) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Number of parameters is imcompatible with caller method "
            << e->get_name() << "." << endl;
        e->set_type(Object);
        return;
    }

    for (unsigned int i = 0; i < signatures.size() - 1; i++) {
        Symbol type_decl = signatures[i];
        Symbol type_actual = actual->nth(i)->get_type();
        Symbol type_decl_infer = formatSelfType(type_decl, currentClass->get_name());
        // Symbol type_actual_infer = formatSelfType(type_actual, static_type);
        Symbol type_actual_infer = formatSelfType(type_actual, currentClass->get_name());

        if (!classTable->is_child(type_actual_infer, type_decl_infer)) {
            method_class *method = classTable->get_method(type_actual_infer, e->get_name());
            formal_class *formal = (formal_class*)method->get_formals()->nth(i);
            classTable->semant_error(currentClass->get_filename(), e)
                << "Type of parameter " << formal->get_name()
                << " is " << type_actual_infer
                << ", which doesnot conform to the declared type " << type_decl
                << "." << endl;
            e->set_type(Object);
            return;
        }
    }

    Symbol return_type = formatSelfType(
        signatures[signatures.size() - 1],
        type_caller);
    e->set_type(return_type);
}

void semanVisitor::visit(dispatch_class *e)
{
    visit(e->get_expr());
    Expressions actual = e->get_actual();
    for (int i = actual->first(); actual->more(i); i = actual->next(i)) {
        visit((Expression_class*)actual->nth(i));
    }

    Symbol type_caller = e->get_expr()->get_type();
    Symbol type_caller_infer = formatSelfType(type_caller, currentClass->get_name());

    if (!classTable->method_exists(type_caller_infer, e->get_name())) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Cannot dispatch to undefined method " << e->get_name() << endl;
        e->set_type(Object);
        return;
    }

    vector<Symbol> signatures = classTable->get_signatures(type_caller_infer, e->get_name());
    if ((signed int)signatures.size() - 1 != actual->len()) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Number of parameters is imcompatible with caller method " << e->get_name() << endl;
        e->set_type(Object);
        return;
    }

    for (unsigned int i = 0; i < signatures.size() - 1; i++) {
        Symbol type_decl = signatures[i];
        Symbol type_actual = actual->nth(i)->get_type();
        Symbol type_decl_infer = formatSelfType(type_decl, currentClass->get_name());
        Symbol type_actual_infer = formatSelfType(type_actual, currentClass->get_name());

        if (!classTable->is_child(type_actual_infer, type_decl_infer)) {
            method_class *method = classTable->get_method(type_caller_infer, e->get_name());
            formal_class *formal = (formal_class*) method->get_formals()->nth(i);
            classTable->semant_error(currentClass->get_filename(), actual->nth(i))
                << "Type of parameter " << formal->get_name()
                << " of called method " << e->get_name()
                << " is " << type_actual_infer
                << ", which doesnot conform to the decalred type." << endl;
            e->set_type(Object);
            return;
        }
    }

    Symbol type_return = formatSelfType(
        signatures[signatures.size() - 1],
        type_caller);
    e->set_type(type_return);
}

void semanVisitor::visit(cond_class *e)
{
    visit(e->get_pred());
    Symbol type_pred = e->get_pred()->get_type();
    if (type_pred != Bool) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Type of pred must be Bool." << endl;
        e->set_type(Object);
        return;
    }

    visit(e->get_then_exp());
    visit(e->get_else_exp());
    Symbol type_then = e->get_then_exp()->get_type();
    Symbol type_else = e->get_else_exp()->get_type();

    if (type_then == SELF_TYPE && type_else == SELF_TYPE) {
        e->set_type(SELF_TYPE);
        return;
    }

    Symbol type_then_infer = formatSelfType(type_then, currentClass->get_name());
    Symbol type_else_infer = formatSelfType(type_else, currentClass->get_name());
    Symbol type_cond = classTable->least_upper_bound(type_then_infer, type_else_infer);
    e->set_type(type_cond);
}

void semanVisitor::visit(loop_class *e)
{
    visit(e->get_pred());
    visit(e->get_body());

    Symbol type_pred = e->get_pred()->get_type();
    if (type_pred != Bool) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Type of prediction must be Bool." << endl;
        e->set_type(Object);
        return;
    }

    e->set_type(Object);
}

void semanVisitor::visit(typcase_class *e)
{
    visit(e->get_expr());
    Cases cases = e->get_cases();
    if (cases->len() == 0) {
        // classTable->semant_error(currentClass->get_filename(), e)
        //     << "Case expression must have at least one branch." << endl;
        e->set_type(Object);
        return;
    }

    for (int i = 0; i < cases->len(); i++) {
        branch_class *b = (branch_class*)cases->nth(i);
        if (b->get_name() == self) {
            classTable->semant_error(currentClass->get_filename(), e)
                << "'self' cannot be bound in case." << endl;
            e->set_type(Object);
            return;
        }
        visit(b);
    }

    for (int i = 0; i < cases->len(); i++) {
        for (int j = i + 1; j < cases->len(); j++) {
            branch_class *bi = (branch_class*)cases->nth(i);
            branch_class *bj = (branch_class*)cases->nth(j);
            if (bi->get_type_decl() == bj->get_type_decl()) {
                classTable->semant_error(currentClass->get_filename(), e)
                    << "Branch " << bi->get_type_decl()
                    << "is duplicated in case." << endl;
                e->set_type(Object);
                return;
            }
        }
    }

    // ->get_type_decl()
    Symbol type = ((branch_class*)cases->nth(0))->get_expr()->get_type();
    type = formatSelfType(type, currentClass->get_name());
    bool all_self_type = true;
    for (int i = 0; i < cases->len(); i++) {
        Symbol ti = ((branch_class*)cases->nth(i))->get_expr()->get_type();
        if (ti == SELF_TYPE) {
            ti = currentClass->get_name();
        } else {
            all_self_type = false;
        }
        type = classTable->least_upper_bound(type, ti);
    }

    if (all_self_type) {
        e->set_type(SELF_TYPE);
    } else {
        e->set_type(type);
    }
}

void semanVisitor::visit(block_class *e)
{
    Expressions body = e->get_body();
    for (int i = 0; i < body->len(); i++) {
        visit((Expression_class*)body->nth(i));
    }

    Symbol type = body->nth(body->len() - 1)->get_type();
    e->set_type(type);
}

void semanVisitor::visit(let_class *e)
{
    if (e->get_identifier() == self) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "'self' cannot be bound in let." << endl;
        e->set_type(Object);
        return;
    }
    visit(e->get_init());

    Symbol type_decl = e->get_type_decl();
    Symbol type_decl_infer = formatSelfType(type_decl, currentClass->get_name());

    if (typeid((e->get_init())) != typeid(no_expr_class)) {
        Symbol type_actual = e->get_init()->get_type();
        Symbol type_actual_infer = formatSelfType(type_actual, currentClass->get_name());

        // (outofscope)	 Using a name that exists but is out of scope
        if (type_actual_infer != NULL && !classTable->is_child(type_actual_infer, type_decl_infer)) {
            classTable->semant_error(currentClass->get_filename(), e)
                << "Initialization type of id is " << type_actual
                << ", which doesnot conform to the declared type." << endl;
            e->set_type(Object);
            return;
        }
    }

    enterscope();
    // addId(e->get_identifier(), e->get_init(), false);
    addId(e->get_identifier(), e, false);
    visit(e->get_body());
    exitscope();
    
    Symbol type_return = e->get_body()->get_type();
    e->set_type(type_return);
}

void semanVisitor::visit(plus_class *e)
{
    visit(e->get_e1());
    visit(e->get_e2());

    Symbol type1 = e->get_e1()->get_type();
    Symbol type2 = e->get_e2()->get_type();

    if (type1 == Int && type2 == Int) {
        e->set_type(Int);
    } else {
        classTable->semant_error(currentClass->get_filename(), e)
            << "No-Int parameters for "
            << type1 << " + " << type2 << "." << endl;
        e->set_type(Object);
    }
}

void semanVisitor::visit(sub_class *e)
{
    visit(e->get_e1());
    visit(e->get_e2());

    Symbol type1 = e->get_e1()->get_type();
    Symbol type2 = e->get_e2()->get_type();

    if (type1 == Int && type2 == Int) {
        e->set_type(Int);
    } else {
        classTable->semant_error(currentClass->get_filename(), e)
            << "No-Int parameters for "
            << type1 << " - " << type2 << "." << endl;
        e->set_type(Object);
    }
}

void semanVisitor::visit(mul_class *e)
{
    visit(e->get_e1());
    visit(e->get_e2());

    Symbol type1 = e->get_e1()->get_type();
    Symbol type2 = e->get_e2()->get_type();

    if (type1 == Int && type2 == Int) {
        e->set_type(Int);
    } else {
        classTable->semant_error(currentClass->get_filename(), e)
            << "No-Int parameters for "
            << type1 << " * " << type2 << "." << endl;
        e->set_type(Object);
    }
}

void semanVisitor::visit(divide_class *e)
{
    visit(e->get_e1());
    visit(e->get_e2());

    Symbol type1 = e->get_e1()->get_type();
    Symbol type2 = e->get_e2()->get_type();

    if (type1 == Int && type2 == Int) {
        e->set_type(Int);
    } else {
        classTable->semant_error(currentClass->get_filename(), e)
            << "No-Int parameters for "
            << type1 << " / " << type2 << "." << endl;
        e->set_type(Object);
    }
}

void semanVisitor::visit(neg_class *e)
{
    visit(e->get_e1());

    Symbol type1 = e->get_e1()->get_type();
    if (type1 == Int) {
        e->set_type(Int);
    } else {
        classTable->semant_error(currentClass->get_filename(), e)
            << "No-Int parameterf for -" << type1 << "." << endl;
        e->set_type(Object);
    }
}

void semanVisitor::visit(lt_class *e)
{
    visit(e->get_e1());
    visit(e->get_e2());

    Symbol type1 = e->get_e1()->get_type();
    Symbol type2 = e->get_e2()->get_type();

    if (type1 == Int && type2 == Int) {
        e->set_type(Bool);
    } else {
        classTable->semant_error(currentClass->get_filename(), e)
            << "No-Int parameters for "
            << type1 << " < " << type2 << "." << endl;
        e->set_type(Object);
    }
}

void semanVisitor::visit(eq_class *e)
{
    visit(e->get_e1());
    visit(e->get_e2());

    Symbol type1 = e->get_e1()->get_type();
    Symbol type2 = e->get_e2()->get_type();

    bool base1 = type1 == Int || type1 == Bool || type1 == Str;
    bool base2 = type2 == Int || type2 == Bool || type2 == Str;

    bool imcompatible_base_type = base1 && base2 && type1 != type2;
    bool not_all_base_type = base1 != base2;

    if (imcompatible_base_type || not_all_base_type) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Illegal comparision with basic types." << endl;
        e->set_type(Object);
        return;
    }
    e->set_type(Bool);
}

void semanVisitor::visit(leq_class *e)
{
    visit(e->get_e1());
    visit(e->get_e2());

    Symbol type1 = e->get_e1()->get_type();
    Symbol type2 = e->get_e2()->get_type();

    if (type1 == Int && type2 == Int) {
        e->set_type(Bool);
    } else {
        classTable->semant_error(currentClass->get_filename(), e)
            << "No-Int parameters for "
            << type1 << " <= " << type2 << "." << endl;
        e->set_type(Object);
    }
}

void semanVisitor::visit(comp_class *e)
{
    visit(e->get_e1());

    Symbol type1 = e->get_e1()->get_type();
    if (type1 != Bool) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Illegal argument with type " << type1 << " for ! expression." << endl;
        e->set_type(Object);
        return;
    }
    e->set_type(Bool);
}

void semanVisitor::visit(int_const_class *e)
{
    inttable.add_int(atoi(e->get_token()->get_string()));
    e->set_type(Int);
}

void semanVisitor::visit(bool_const_class *e)
{
    e->set_type(Bool);
}

void semanVisitor::visit(string_const_class *e)
{
    stringtable.add_string(e->get_token()->get_string());
    e->set_type(Str);
}

void semanVisitor::visit(new__class *e)
{
    Symbol type_name = e->get_type_name();

    if (type_name != SELF_TYPE && !classTable->class_exists(type_name)) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "Cannot use 'new' with undefined class." << endl;
        e->set_type(Object);
        return;
    }
    // if (type_name == SELF_TYPE) {
    //     e->set_type(currentClass->get_name());
    // } else {
    //     e->set_type(type_name);
    // }
    e->set_type(type_name);
}

void semanVisitor::visit(isvoid_class *e)
{
    visit(e->get_e1());
    e->set_type(Bool);
}

void semanVisitor::visit(no_expr_class *e)
{
}

void semanVisitor::visit(object_class *e)
{
    Symbol name = e->get_name();
    if (name == self) {
        e->set_type(SELF_TYPE);
        return;
    }

    tree_node *t = lookupObject(name);
    if (t == NULL) {
        classTable->semant_error(currentClass->get_filename(), e)
            << "identifier " << name << " is undefined." << endl;
        e->set_type(Object);
        return;
    }

    Symbol type = NULL;
    if (typeid(*t) == typeid(attr_class)) {
        type = ((attr_class*)t)->get_type_decl();
    } else if (typeid(*t) == typeid(formal_class)) {
        type = ((formal_class*)t)->get_type_decl();
    } else if (typeid(*t) == typeid(let_class)) {
        type = ((let_class*)t)->get_type_decl();
    } else if (typeid(*t) == typeid(branch_class)) {
        type = ((branch_class*)t)->get_type_decl();
    }

    e->set_type(type);
}

/**************************************************************/
/*                   Accept function                          */
/**************************************************************/

void program_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    for (int i = classes->first(); classes->more(i); i = classes->next(i)) {
        class__class *cls = (class__class*)classes->nth(i);
        cls->accept(v);
    }
    v->exitscope();
}

void class__class::accept(Visitor *v)
{
    v->enterscope();
    semanVisitor *sv = (semanVisitor*) v;
    if (parent != No_class) {
        class__class *parentClass_class = sv->classTable->get_parent(name);
        if (parentClass_class != NULL) {
            parentClass_class->add_parentMembers(v, parent_feature_list);
        }
    }

    sv->visit(this);

    for (int i = features->first(); features->more(i); i = features->next(i)) {
        Feature f = (Feature) features->nth(i);
        if (f->get_is_method()) {
            method_class *m = (method_class*) f;
            sv->addId(m->get_name(), m, true);
        } else {
            attr_class *a = (attr_class*) f;
            sv->addId(a->get_name(), a, false);
        }
    }

    for (int i = parent_feature_list->first(); parent_feature_list->more(i); i = parent_feature_list->next(i)) {
        Feature f = (Feature) parent_feature_list->nth(i);
        if (f->get_is_method()) {
            method_class *m = (method_class*) f;
            tree_node *t = sv->probeMethod(m->get_name());
            if (t == NULL || typeid(*t) != typeid(method_class)) {
                sv->addId(m->get_name(), m, true);
            }
        } else {
            attr_class *a = (attr_class*) f;
            tree_node *t = sv->probeObject(a->get_name());
            if (t == NULL || typeid(*t) != typeid(attr_class)) {
                sv->addId(a->get_name(), a, false);
            }
        }
    }

    for (int i = features->first(); features->more(i); i = features->next(i)) {
        Feature f = (Feature) features->nth(i);
        if (f->get_is_method()) {
            method_class *m = (method_class*) f;
            m->accept(v);
        } else {
            attr_class *a = (attr_class*) f;
            a->accept(v);
        }
    }

    v->exitscope();
}

void class__class::add_parentMembers(Visitor *v, Features &parent_feature_list)
{
    semanVisitor *sv = (semanVisitor*) v;
    for (int i = features->first(); features->more(i); i = features->next(i)) {
        Feature f = (Feature) features->nth(i);
        if (f->get_is_method()) {
            method_class *m = (method_class*) f;
            parent_feature_list = append_Features(single_Features(m), parent_feature_list);
        } else {
            attr_class *a = (attr_class*) f;
            parent_feature_list = append_Features(single_Features(a), parent_feature_list);
        }
    }

    if (parent != No_class) {
        class__class *parentClass_class = sv->classTable->get_parent(name);
        parentClass_class->add_parentMembers(sv, parent_feature_list);
    }
}

void method_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    for (int i = formals->first(); formals->more(i); i = formals->next(i)) {
        formal_class *f = (formal_class*) formals->nth(i);
        f->accept(v);
    }
    v->exitscope();
}

void attr_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    v->exitscope();
}

void formal_class::accept(Visitor *v)
{
    v->visit(this);
}

void Expression_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    v->exitscope();
}

void branch_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    expr->accept(v);
    v->exitscope();
}

void assign_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    // expr->accept(v);
    v->exitscope();
}

void static_dispatch_class::accept(Visitor *v)
{
    v->enterscope();
    // ca
    v->visit(this);
    expr->accept(v);
    for (int i = actual->first(); actual->more(i); i = actual->next(i)) {
        ((Expression_class*)actual->nth(i))->accept(v);
    }
    v->exitscope();
}

void dispatch_class::accept(Visitor *v)
{
    v->enterscope();
    // ca
    v->visit(this);
    expr->accept(v);
    for (int i = actual->first(); actual->more(i); i = actual->next(i)) {
        ((Expression_class*)actual->nth(i))->accept(v);
    }
    v->exitscope();
}

void cond_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    pred->accept(v);
    then_exp->accept(v);
    else_exp->accept(v);
    v->exitscope();
}

void loop_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    pred->accept(v);
    body->accept(v);
    v->exitscope();
}

void typcase_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    expr->accept(v);
    for (int i = cases->first(); cases->more(i); i = cases->next(i)) {
        ((branch_class*)cases->nth(i))->accept(v);
    }
    v->exitscope();
}

void block_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    // for (int i = body->first(); body->more(i); i = body->next(i)) {
    //     ((Expression_class*)body->nth(i))->accept(v);
    // }
    v->exitscope();
}

void let_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    // init->accept(v);
    // body->accept(v);
    v->exitscope();
}

void plus_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    e1->accept(v);
    e2->accept(v);
    v->exitscope();
}

void sub_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    e1->accept(v);
    e2->accept(v);
    v->exitscope();
}

void mul_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    e1->accept(v);
    e2->accept(v);
    v->exitscope();
}

void divide_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    e1->accept(v);
    e2->accept(v);
    v->exitscope();
}

void neg_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    e1->accept(v);
    v->exitscope();
}

void lt_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    e1->accept(v);
    e2->accept(v);
    v->exitscope();
}

void eq_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    e1->accept(v);
    e2->accept(v);
    v->exitscope();
}

void leq_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    e1->accept(v);
    e2->accept(v);
    v->exitscope();
}

void comp_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    e1->accept(v);
    v->exitscope();
}

void int_const_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    v->exitscope();
}

void bool_const_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    v->exitscope();
}

void string_const_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    v->exitscope();
}

void new__class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    v->exitscope();
}

void isvoid_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    e1->accept(v);
    v->exitscope();
}

void no_expr_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    v->exitscope();
}

void object_class::accept(Visitor *v)
{
    v->enterscope();
    v->visit(this);
    v->exitscope();
}
