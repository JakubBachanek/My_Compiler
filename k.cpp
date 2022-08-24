#include "k_lib.h"

#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>
#include <string.h>
#include <math.h>
#include <limits.h>
#include <string>
#include <cstring>
#include <fstream>
#include <iostream>
using namespace std;

SymbolTable* sym_table;
unsigned long long m_index;
AstNode* program_ast;
TAC_program* program_tac;
TAC_program* program_tac_o;
int l_index = 1;
int i_index = -1;
int i_num_index = -1;
int i_scope = 0;
int i_previous[50][2];
Register reg[6];

RMC_program* program_rmc;
ofstream output_file;

void sym_table_init(void) {
    sym_table = (SymbolTable*) malloc(sizeof(SymbolTable));
    sym_table->max_size = MAX_SIZE;
    sym_table->size = 0;
    sym_table->symbols = (Symbol*) malloc(sizeof(Symbol) * MAX_SIZE);
    m_index = 0;
    for(int i = 0; i < 50; i++) {
        i_previous[i][0] = -1;
        i_previous[i][1] = -1;
    }
}

void error_1(char* name, int lineno) {
    cout << "ERROR 1 - druga deklaracja zmiennej \"" << name << "\" w linii " << lineno << endl;
    exit(1111);
}

void error_2(void) {
    cout << "ERROR 2" << endl;
    exit(1112);
}

void error_3(char* name, int lineno) {
    cout << "ERROR 3 - użycie niezadeklarowanej zmiennej \"" << name << "\" w linii " << lineno << endl;
    exit(1113);
}

void error_4(char* name, int lineno) {
    cout << "ERROR 4 - niewłaściwe użycie zmiennej tablicowej \"" << name << "\" w linii " << lineno << endl;
    exit(1114);
}

void error_5(char* name, int lineno) {
    cout << "ERROR 5 - niewłaściwe użycie zmiennej \"" << name << "\" w linii " << lineno << endl;
    exit(1214);
}

void error_6(char* name, int lineno) {
    cout << "ERROR 6 - użycie niezainicjalizowanej zmiennej \"" << name << "\" w linii " << lineno << endl;
    exit(1215);
}

void error_7(char* name, int lineno) {
    cout << "ERROR 7 - użycie niezadeklarowanej zmiennej \"" << name << "\" o tej samej nazwie co iterator, w linii " << lineno << endl;
    exit(1216);
}

void error_8(int lineno) {
    cout << "ERROR 8 - modyfikacja iteratora w pętli w linii " << lineno << endl;
    exit(1217);
}

void error_type_settings(void) {
    cout << "ERROR - type settings" << endl;
    exit(1115);
}

void error_arr_range(char* name) {
    cout << "ERROR - niewłaściwy zakres tablicy " << name << endl;
    exit(1116);
}


int check_declared(char* name) {
    int size = sym_table->size;
    
    for(int i = 0; i < size; i++) {
        if(!strcmp(sym_table->symbols[i].name, name)) {
            return i;
        }
    }
    return -1;
}

int check_var_decl(char* name) {
    int size = sym_table->size;
    int temp = -1;
    for(int i = 0; i < size; i++) {
        if(!strcmp(sym_table->symbols[i].name, name)) {
            if(sym_table->symbols[i].type == ITER && !(sym_table->symbols[i].is_initialized)) {
                return -1;
            }
            temp = i;
        }
    }

    if(temp < 0) {
        return -1;
    }
    
    if(sym_table->symbols[temp].type == ARR) {
        return -2;
    }

    return temp;
}

bool check_var_init(int index) {
    if(sym_table->symbols[index].is_initialized) {
        return true;
    }

    return false;
}

int check_arr_decl(char* name) {
    int size = sym_table->size;
    int temp = -1;
    
    for(int i = 0; i < size; i++) {
        if(!strcmp(sym_table->symbols[i].name, name)) {
            temp = i;
        }
    }

    if(temp < 0) {
        return -1;
    }
    
    if(sym_table->symbols[temp].type != ARR) {
        return -2;
    }

    return temp;
}


int check_iter_declared(char* name, int scope) {
    int size = sym_table->size;
    
    for(int i = 0; i < size; i++) {
        if(!strcmp(sym_table->symbols[i].name, name) && sym_table->symbols[i].type == ITER) {
            if(sym_table->symbols[i].scope >= scope || !(sym_table->symbols[i].is_initialized)) {
                sym_table->symbols[i].is_initialized = true;
                return i;
            } else {
                return -2;
            }
        }
    }
    return -1;
}

bool check_iter_loop(int index, AstNode* node_1, AstNode* node_2) {
    if((node_1->type == AST_VAR && node_1->sym_index == index)
        || (node_2->type == AST_VAR && node_2->sym_index == index)) {
        return true;        
    } else if(node_1->type == AST_ARR && (node_1->nodes[0]->sym_index == index || node_1->nodes[1]->sym_index == index)) {
        return true;
    } else if(node_2->type == AST_ARR && (node_2->nodes[0]->sym_index == index || node_2->nodes[1]->sym_index == index)) {
        return true;
    }
    return false;
}

bool check_iter_modified(AstNode* node) {
    if(node->type == AST_VAR) {
        int temp = node->sym_index;
        if(temp >= 0 && sym_table->symbols[temp].type == ITER) {
            return true;
        }
    }
    return false;
}

void manage_scope(int scope) {
    int size = sym_table->size;
    
    for(int i = 0; i < size; i++) {
        if(sym_table->symbols[i].type == ITER && sym_table->symbols[i].scope == scope) {
            sym_table->symbols[i].is_initialized = false;
        }
    }
}


int check_num_symbol(char* name) {
    int size = sym_table->size;
    
    for(int i = 0; i < size; i++) {
        if(!strcmp(sym_table->symbols[i].name, name) && sym_table->symbols[i].type == NUMB) {
            return i;
        }
    }
    return -1;
}


void check_extend(void) {
    if((sym_table->size + 1) == sym_table->max_size) {
        sym_table->max_size *= 2;
        Symbol* temp = (Symbol*) realloc(sym_table->symbols, sizeof(Symbol) * sym_table->max_size);
        
        if(temp == NULL) {
            cout << "Memory reallocation failed!" << endl;
            exit(101);
        }

        sym_table->symbols = temp;
    }
}


int add_symbol(char* name) {
    int temp = check_declared(name);

    if(temp >= 0) {
        return -1;
    }
    
    check_extend();
    int size = sym_table->size;
    sym_table->symbols[size].type = NONE;
    int lenlen = strlen(name) + 1;
    sym_table->symbols[size].name = (char*) malloc(lenlen);

    if(sym_table->symbols[size].name == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(102);
    }
    
    strcpy(sym_table->symbols[size].name, name);
    sym_table->size++;
    return size;
}


int add_iter_symbol(char* name, int scope) {
    int temp = check_iter_declared(name, scope);

    if(temp >= 0) {
        return temp;
    } else if(temp == -2) {
        return -1;
    }
    
    check_extend();
    int size = sym_table->size;
    sym_table->symbols[size].type = ITER;
    sym_table->symbols[size].name = (char*) malloc(strlen(name) + 1);
    sym_table->symbols[size].is_initialized = true;
    sym_table->symbols[size].scope = scope;
    sym_table->symbols[size+1].type = ITER;
    sym_table->symbols[size+1].name = (char*) malloc(strlen(name) + 2);
    sym_table->symbols[size+1].is_initialized = true;
    sym_table->symbols[size+1].scope = scope;
    
    if(sym_table->symbols[size].name == NULL || sym_table->symbols[size+1].name == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(103);
    }

    strcpy(sym_table->symbols[size].name, name);
    sprintf(sym_table->symbols[size+1].name, "%sX", name);
    sym_table->size += 2;
    return size;
}


int add_num_symbol(char* name) {
    int temp = check_num_symbol(name);
    
    if(temp >= 0) {
        return temp;
    }
    
    check_extend();
    int size = sym_table->size;
    sym_table->symbols[size].type = NUMB;
    sym_table->symbols[size].num_in_mem = false;
    sym_table->symbols[size].name = (char*) malloc(strlen(name) + 1);
    
    if(sym_table->symbols[size].name == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(104);
    }
    strcpy(sym_table->symbols[size].name, name);
    char* end_ptr;
    unsigned long long temp_2 = strtoull(name, &end_ptr, 10);

    if(*end_ptr) {
        cout << "Unable to convert to ull!" << endl;
        exit(105);
    }

    sym_table->symbols[size].value = temp_2;
    sym_table->size++;
    return size;
}

int add_iter_num_symbol(char* name) {
    check_extend();
    int size = sym_table->size;
    sym_table->symbols[size].type = NUMB;
    sym_table->symbols[size].num_in_mem = false;
    sym_table->symbols[size].name = (char*) malloc(strlen(name) + 1);
    
    if(sym_table->symbols[size].name == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(104);
    }

    strcpy(sym_table->symbols[size].name, name);
    char* end_ptr;
    name[strlen(name)-1] = '\0';
    unsigned long long temp_2 = strtoull(name, &end_ptr, 10);

    if(*end_ptr) {
        cout << "Unable to convert to ull!" << endl;
        exit(105);
    }

    sym_table->symbols[size].value = temp_2;
    sym_table->size++;
    return size;
}

bool set_symbol_type(int index) {
    if(sym_table->size <= index) {
        return false;
    }

    sym_table->symbols[index].type = VAR;
    sym_table->symbols[index].is_initialized = false;
    return true;
}


bool set_symbol_type(int index, char* start, char* end) {
    char* end_ptr1;
    char* end_ptr2;
    unsigned long long start_num = strtoull(start, &end_ptr1, 10);
    unsigned long long end_num = strtoull(end, &end_ptr2, 10);

    if(*end_ptr1 || *end_ptr2) {
        cout << "Unable to convert to ull!" << endl;
        exit(105);
    }

    if(start_num > end_num || sym_table->size <= index) {
        return false;
    }
    
    sym_table->symbols[index].type = ARR;
    sym_table->symbols[index].size = end_num - start_num + 1;
    sym_table->symbols[index].offset = start_num;
    return true;
}

unsigned long long get_mem_arr_address(int arr_index, unsigned long long index_value) { // zwraca prawdziwy adres komorki z tablicy, UWAGA: MOZE PISAC PO PAMIECI
    unsigned long long temp = index_value - sym_table->symbols[arr_index].offset;
    temp += sym_table->symbols[arr_index].mem_i;
    
    return temp;
}

unsigned long long get_mem_address(int index) {
    return sym_table->symbols[index].mem_i;
}

void set_mems(void) {
    for(int i = 0; i < sym_table->size; i++) {
        s_type type = sym_table->symbols[i].type;

        if(type == VAR) {
            sym_table->symbols[i].mem_i = m_index;
            m_index++;
        }
    }
    
    for(int i = 0; i < sym_table->size; i++) {
        s_type type = sym_table->symbols[i].type;

        if(type == ITER) {
            sym_table->symbols[i].mem_i = m_index;
            m_index++;
        }
    }

    for(int i = 0; i < sym_table->size; i++) {
        s_type type = sym_table->symbols[i].type;

        if(type == ARR) {
            sym_table->symbols[i].mem_i = m_index;
            m_index += sym_table->symbols[i].size;
        }
    }
    
    for(int i = 0; i < sym_table->size; i++) {
        s_type type = sym_table->symbols[i].type;

        if(type == NUMB) {
            sym_table->symbols[i].mem_i = m_index;
            m_index++;
        }
    }
}

// #######################################################################
// #######################################################################
// #######################################################################

//                         AST TREE

// #######################################################################
// #######################################################################
// #######################################################################

AstNode* init_commands_node(void) {
    AstNode* node = (AstNode*) malloc(sizeof(AstNode));

    if(node == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(106);
    }
    
    node->max_size = NODE_MAX_SIZE;
    node->type = AST_COMMANDS;
    node->size = 0;
    node->sym_index = -1;
    node->nodes = (AstNode**) malloc(sizeof(AstNode*) * NODE_MAX_SIZE);

    if(node->nodes == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(107);
    }
    
    return node;
}

void check_extend_ast(AstNode* node) {
    if(node->size == node->max_size) {
        node->max_size *= 2;
        AstNode** temp = (AstNode**) realloc(node->nodes, sizeof(AstNode) * node->max_size);
        
        if(temp == NULL) {
            cout << "Memory reallocation failed!" << endl;
            exit(108);
        }
        
        node->nodes = temp;
    }
}

AstNode* add_command(AstNode* node_p, AstNode* node_c) {
    check_extend_ast(node_p);
    node_p->nodes[node_p->size] = node_c;
    node_p->size++;
    
    return node_p;
}

AstNode* init_par_node(ast_node_type type, AstNode* node_1) {
    AstNode* node = (AstNode*) malloc(sizeof(AstNode));
    
    if(node == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(1099);
    }
    
    node->max_size = 1;
    node->type = type;
    node->size = 1;
    node->sym_index = -1;
    node->nodes = (AstNode**) malloc(sizeof(AstNode*));
    
    if(node->nodes == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(1109);
    }
    
    node->nodes[0] = node_1;
    
    return node;
}

AstNode* init_par_node(ast_node_type type, AstNode* node_1, AstNode* node_2) {
    AstNode* node = (AstNode*) malloc(sizeof(AstNode));
    
    if(node == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(109);
    }
    
    node->max_size = 2;
    node->type = type;
    node->size = 2;
    node->sym_index = -1;
    node->nodes = (AstNode**) malloc(sizeof(AstNode*) * 2);
    
    if(node->nodes == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(110);
    }
    
    node->nodes[0] = node_1;
    node->nodes[1] = node_2;
    
    return node;
}


AstNode* init_par_node(ast_node_type type, AstNode* node_1, AstNode* node_2, AstNode* node_3) {
    AstNode* node = (AstNode*) malloc(sizeof(AstNode));
    
    if(node == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(111);
    }
    
    node->max_size = 3;
    node->type = type;
    node->size = 3;
    node->sym_index = -1;
    node->nodes = (AstNode**) malloc(sizeof(AstNode*) * 3);
    
    if(node->nodes == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(112);
    }
    
    node->nodes[0] = node_1;
    node->nodes[1] = node_2;
    node->nodes[2] = node_3;
    
    return node;
}


AstNode* init_par_node(ast_node_type type, AstNode* node_1, AstNode* node_2, AstNode* node_3, AstNode* node_4, AstNode* node_5) {
    AstNode* node = (AstNode*) malloc(sizeof(AstNode));
    
    if(node == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(113);
    }
    
    node->max_size = 5;
    node->type = type;
    node->size = 5;
    node->sym_index = -1;
    node->nodes = (AstNode**) malloc(sizeof(AstNode*) * 5);
    
    if(node->nodes == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(114);
    }
    
    node->nodes[0] = node_1;
    node->nodes[1] = node_2;
    node->nodes[2] = node_3;
    node->nodes[3] = node_4;
    node->nodes[4] = node_5;
    
    return node;
}


AstNode* init_num_node(ast_node_type type, int index) {
    AstNode* node = (AstNode*) malloc(sizeof(AstNode));
    
    if(node == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(115);
    }
    
    node->max_size = 1;
    node->type = type;
    node->size = 1;
    node->sym_index = index;
    node->nodes = NULL;
    
    return node;
}

AstNode* init_num_node(ast_node_type type, int index, bool initialized) {
    AstNode* node = (AstNode*) malloc(sizeof(AstNode));
    
    if(node == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(115);
    }
    
    node->max_size = 1;
    node->type = type;
    node->size = 1;
    node->sym_index = index;
    node->nodes = NULL;
    sym_table->symbols[index].is_initialized = initialized;
    
    return node;
}


void build_program_ast(AstNode* node) {
    program_ast = (AstNode*) malloc(sizeof(AstNode));
    
    if(program_ast == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(116);
    }
    
    program_ast->max_size = 1;
    program_ast->type = AST_PROGRAM;
    program_ast->size = 1;
    program_ast->sym_index = -1;
    program_ast->nodes = (AstNode**) malloc(sizeof(AstNode*));
    
    if(program_ast->nodes == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(117);
    }
    
    program_ast->nodes[0] = node;
}


// #######################################################################
// #######################################################################
// #######################################################################

//                         TAC CODE

// #######################################################################
// #######################################################################
// #######################################################################




void init_TAC_program(void) {
    program_tac = (TAC_program*) malloc(sizeof(TAC_program));
    
    if(program_tac == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(118);
    }
    
    program_tac->max_size = TAC_MAX_SIZE;
    program_tac->size = 0;
    program_tac->tac_s = (TAC_I*) malloc(sizeof(TAC_I) * TAC_MAX_SIZE);
    
    if(program_tac->tac_s == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(119);
    }
}


void trans_ast_to_tac(void) {
    ast_to_tac(program_ast);   
}


void check_extend_tac(void) {
    if(program_tac->size == program_tac->max_size) {
        program_tac->max_size *= 2;
        TAC_I* temp = (TAC_I*) realloc(program_tac->tac_s, sizeof(TAC_I) * program_tac->max_size);
        
        if(temp == NULL) {
            cout << "Memory reallocation failed!" << endl;
            exit(120);
        }
        
        program_tac->tac_s = temp;
    }
}


void add_tac_ins(tac_type type) {
    check_extend_tac();
    
    program_tac->tac_s[program_tac->size].type = type;
    program_tac->tac_s[program_tac->size].size = 0;
    program_tac->tac_s[program_tac->size].b_index = -1;
    program_tac->size++;
}

void add_ins_index(int index_1, int index_2) {
    int temp = program_tac->tac_s[program_tac->size-1].size;
    program_tac->tac_s[program_tac->size-1].indexes[temp][0] = index_1;
    program_tac->tac_s[program_tac->size-1].indexes[temp][1] = index_2;
    program_tac->tac_s[program_tac->size-1].size++;
}

void change_tac_ins(tac_type type) {
    program_tac->tac_s[program_tac->size - 1].type = type;
}

void add_label(int index) {
    check_extend_tac();
    
    program_tac->tac_s[program_tac->size].type = TAC_LABEL;
    program_tac->tac_s[program_tac->size].indexes[0][0] = index;
    program_tac->tac_s[program_tac->size].size = 1;
    program_tac->tac_s[program_tac->size].b_index = -1;
    program_tac->size++;
}

void ast_to_tac(AstNode* node) {
    if(node == NULL) {
        return;
    }

    ast_node_type type = node->type;
    int label_start, label_end, label_else, label_temp;
    
    if(type == AST_PROGRAM) {   // OK
        for(int i = 0; i < node->size; i++) {
            ast_to_tac(node->nodes[i]);
        }
    } else if(type == AST_COMMANDS) {   // OK
        for(int i = 0; i < node->size; i++) {
            ast_to_tac(node->nodes[i]);
        }
    } else if(type == AST_ASSIGN) {  // OK
        add_tac_ins(TAC_ASSIGN);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
        
    } else if(type == AST_IF_ELSE) { // OK
        add_tac_ins(TAC_UNDEFINED);
        label_else = l_index;
        label_temp = l_index;
        l_index++;
        label_end = l_index;
        l_index++;
        
        add_ins_index(label_temp, -1);
        ast_to_tac(node->nodes[0]); //condition
        ast_to_tac(node->nodes[1]); //commands if true
        add_tac_ins(TAC_JUMP);
        add_ins_index(label_end, -1);
        add_label(label_else);
        ast_to_tac(node->nodes[2]); //commands if false
        add_label(label_end);
        
    } else if(type == AST_IF) {      // OK
        add_tac_ins(TAC_UNDEFINED);
        label_end = l_index;
        label_temp = l_index;
        l_index++;
        
        add_ins_index(label_temp, -1);
        ast_to_tac(node->nodes[0]); //condition
        ast_to_tac(node->nodes[1]); //commands if true
        add_label(label_end);
        
    } else if(type == AST_WHILE) {
        label_start = l_index;
        l_index++;
        label_end = l_index;
        label_temp = l_index;
        l_index++;
        
        add_label(label_start);
        add_tac_ins(TAC_UNDEFINED);
        add_ins_index(label_temp, -1);
        ast_to_tac(node->nodes[0]); //condition
        ast_to_tac(node->nodes[1]); //commands if true
        add_tac_ins(TAC_JUMP);
        add_ins_index(label_start, -1);
        add_label(label_end);
        
    } else if(type == AST_REPEAT) {   // OK
        label_start = l_index;
        l_index++;
        
        add_label(label_start);
        ast_to_tac(node->nodes[0]); //commands repeat at least once
        add_tac_ins(TAC_UNDEFINED);
        add_ins_index(label_start, -1);
        ast_to_tac(node->nodes[1]); //condition
        
    } else if(type == AST_FOR_TO) {   // OK
        int must_run = 0;
        
        if(node->nodes[2]->type == AST_NUM && node->nodes[3]->type == AST_NUM) {
            int sym_index_1 = node->nodes[2]->sym_index;
            int sym_index_2 = node->nodes[3]->sym_index;
            unsigned long long value_1 = get_sym_value(sym_index_1);
            unsigned long long value_2 = get_sym_value(sym_index_2);
            
            if(value_1 > value_2) {
                must_run = 1;
            } else {
                int iterations = value_2 - value_1 + 1;
                
                if(iterations < 30) {
                    if(i_index >= 0) {
                        i_previous[i_scope][0] = i_index;
                        i_previous[i_scope][1] = i_num_index;
                        i_scope++;
                    }
                    int old = node->nodes[0]->sym_index;
                    i_index = node->nodes[0]->sym_index;
                    
                    for(int i = 0; i < iterations; i++) {
                        unsigned long long new_value = value_1 + i;
                        int num_len = (int) snprintf(NULL, 0, "%llu", new_value);
                        char* temp_name = (char*) malloc(num_len + 2);
                        sprintf(temp_name, "%lluI", new_value);

                        i_num_index = add_iter_num_symbol(temp_name);
                        ast_replace_iterator(node->nodes[4]);
                        ast_to_tac(node->nodes[4]);
                        free(temp_name);
                        i_index = i_num_index;
                    }
                    
                    i_num_index = old;
                    ast_replace_iterator(node->nodes[4]);                    
                    i_scope--;

                    if(i_previous[i_scope][0] >= 0) {
                        i_index = i_previous[i_scope][0];
                        i_num_index = i_previous[i_scope][1];
                    } else {
                        i_index = -1;
                        i_num_index = -1;
                    }
                    must_run = 1;
                }
            }
        }
        
        
        if(must_run == 0) {
            label_start = l_index;
            l_index++;
            label_end = l_index;
            l_index++;
        
            add_tac_ins(TAC_JGT);
            add_ins_index(label_end, -1);
            ast_to_tac(node->nodes[2]);
            ast_to_tac(node->nodes[3]);
        
            add_tac_ins(TAC_ASSIGN);
            ast_to_tac(node->nodes[0]);
            ast_to_tac(node->nodes[2]);
            add_tac_ins(TAC_ASSIGN);
            ast_to_tac(node->nodes[1]);
            ast_to_tac(node->nodes[3]);

            add_tac_ins(TAC_SUB);
            ast_to_tac(node->nodes[1]);
            ast_to_tac(node->nodes[1]);
            ast_to_tac(node->nodes[0]);
            add_tac_ins(TAC_INC);
            ast_to_tac(node->nodes[1]);
        
            add_label(label_start);
            add_tac_ins(TAC_JZERO);
            add_ins_index(label_end, -1);
            ast_to_tac(node->nodes[1]);
            ast_to_tac(node->nodes[4]); // commands
        
            add_tac_ins(TAC_DEC);
            ast_to_tac(node->nodes[1]);
            add_tac_ins(TAC_INC);
            ast_to_tac(node->nodes[0]);

            add_tac_ins(TAC_JUMP);
            add_ins_index(label_start, -1);
            add_label(label_end);
        }
        
    } else if(type == AST_FOR_DOWNTO) { // OK
        int must_run = 0;
        
        if(node->nodes[2]->type == AST_NUM && node->nodes[3]->type == AST_NUM) {
            int sym_index_1 = node->nodes[2]->sym_index;
            int sym_index_2 = node->nodes[3]->sym_index;
            unsigned long long value_1 = get_sym_value(sym_index_1);
            unsigned long long value_2 = get_sym_value(sym_index_2);
            
            if(value_1 < value_2) {
                must_run = 1;
            } else {
                int iterations = value_1 - value_2 + 1;
                
                if(iterations < 30) {
                    if(i_index >= 0) {
                        i_previous[i_scope][0] = i_index;
                        i_previous[i_scope][1] = i_num_index;
                        i_scope++;
                    }
                    int old = node->nodes[0]->sym_index;
                    i_index = node->nodes[0]->sym_index;

                    for(int i = 0; i < iterations; i++) {
                        unsigned long long new_value = value_1 - i;
                        int num_len = (int) snprintf(NULL, 0, "%llu", new_value);
                        char* temp_name = (char*) malloc(num_len + 2);
                        sprintf(temp_name, "%lluI", new_value);

                        i_num_index = add_iter_num_symbol(temp_name);
                        ast_replace_iterator(node->nodes[4]);
                        ast_to_tac(node->nodes[4]);
                        free(temp_name);
                        i_index = i_num_index;
                    }
                    
                    i_num_index = old;
                    ast_replace_iterator(node->nodes[4]);                    
                    i_scope--;

                    if(i_previous[i_scope][0] >= 0) {
                        i_index = i_previous[i_scope][0];
                        i_num_index = i_previous[i_scope][1];
                    } else {
                        i_index = -1;
                        i_num_index = -1;
                    }  
                    must_run = 1;
                }
            }
        }
        
        if(must_run == 0) {
            label_start = l_index;
            l_index++;
            label_end = l_index;
            l_index++;

            add_tac_ins(TAC_JLT);
            add_ins_index(label_end, -1);
            ast_to_tac(node->nodes[2]);
            ast_to_tac(node->nodes[3]);

            add_tac_ins(TAC_ASSIGN);
            ast_to_tac(node->nodes[0]);
            ast_to_tac(node->nodes[2]);
            add_tac_ins(TAC_ASSIGN);
            ast_to_tac(node->nodes[1]);
            ast_to_tac(node->nodes[2]);

            add_tac_ins(TAC_SUB);
            ast_to_tac(node->nodes[1]);
            ast_to_tac(node->nodes[1]);
            ast_to_tac(node->nodes[3]);
            add_tac_ins(TAC_INC);
            ast_to_tac(node->nodes[1]);

            add_label(label_start);
            add_tac_ins(TAC_JZERO);
            add_ins_index(label_end, -1);
            ast_to_tac(node->nodes[1]);
            ast_to_tac(node->nodes[4]); // commands

            add_tac_ins(TAC_DEC);
            ast_to_tac(node->nodes[0]);
            add_tac_ins(TAC_DEC);
            ast_to_tac(node->nodes[1]);

            add_tac_ins(TAC_JUMP);
            add_ins_index(label_start, -1);
            add_label(label_end);
        }
        
    } else if(type == AST_READ) {   // OK
        add_tac_ins(TAC_READ);
        ast_to_tac(node->nodes[0]);
    } else if(type == AST_WRITE) {   // OK
        add_tac_ins(TAC_WRITE);
        ast_to_tac(node->nodes[0]);
    } else if(type == AST_ADD) {   // OK
        change_tac_ins(TAC_ADD);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
    } else if(type == AST_SUB) {   // OK
        change_tac_ins(TAC_SUB);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
    } else if(type == AST_MUL) {   // OK
        change_tac_ins(TAC_MUL);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
    } else if(type == AST_DIV) {   // OK
        change_tac_ins(TAC_DIV);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
    } else if(type == AST_MOD) {   // OK
        change_tac_ins(TAC_MOD);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
    } else if(type == AST_EQ) {   // OK
        change_tac_ins(TAC_JNEQ);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
    } else if(type == AST_NEQ) {   // OK
        change_tac_ins(TAC_JEQ);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
    } else if(type == AST_LT) {   // OK
        change_tac_ins(TAC_JGEQ);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
    } else if(type == AST_GT) {   // OK
        change_tac_ins(TAC_JLEQ);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
    } else if(type == AST_LEQ) {     // OK
        change_tac_ins(TAC_JGT);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
    } else if(type == AST_GEQ) {    // OK
        change_tac_ins(TAC_JLT);
        ast_to_tac(node->nodes[0]);
        ast_to_tac(node->nodes[1]);
    } else if(type == AST_NUM) { // OK
        add_ins_index(node->sym_index, -1);
    } else if(type == AST_VAR) { // OK
        add_ins_index(node->sym_index, -1);
    } else if(type == AST_ARR) { // OK
        add_ins_index(node->nodes[0]->sym_index, node->nodes[1]->sym_index);
    }
}

void ast_replace_iterator(AstNode* node) {
    if(node == NULL) {
        return;
    }

    ast_node_type type = node->type;
    
    if(type == AST_COMMANDS) {   // OK
        for(int i = 0; i < node->size; i++) {
            ast_replace_iterator(node->nodes[i]);
        }
    } else if(type == AST_ASSIGN) {  // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
        
    } else if(type == AST_IF_ELSE) { // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
        ast_replace_iterator(node->nodes[2]); //commands if false
        
    } else if(type == AST_IF) {      // OK
        ast_replace_iterator(node->nodes[0]); //condition
        ast_replace_iterator(node->nodes[1]); //commands if true
        
    } else if(type == AST_WHILE) {
        ast_replace_iterator(node->nodes[0]); //condition
        ast_replace_iterator(node->nodes[1]); //commands if true
        
    } else if(type == AST_REPEAT) {   // OK
        ast_replace_iterator(node->nodes[0]); //commands repeat at least once
        ast_replace_iterator(node->nodes[1]); //condition
        
    } else if(type == AST_FOR_TO) {   // OK
        ast_replace_iterator(node->nodes[2]);
        ast_replace_iterator(node->nodes[3]);
        ast_replace_iterator(node->nodes[4]); // commands
        
    } else if(type == AST_FOR_DOWNTO) { // OK
        ast_replace_iterator(node->nodes[2]);
        ast_replace_iterator(node->nodes[3]);
        ast_replace_iterator(node->nodes[4]); // commands
        
    } else if(type == AST_WRITE) {   // OK
        ast_replace_iterator(node->nodes[0]);
    } else if(type == AST_ADD) {   // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
    } else if(type == AST_SUB) {   // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
    } else if(type == AST_MUL) {   // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
    } else if(type == AST_DIV) {   // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
    } else if(type == AST_MOD) {   // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
    } else if(type == AST_EQ) {   // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
    } else if(type == AST_NEQ) {   // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
    } else if(type == AST_LT) {   // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
    } else if(type == AST_GT) {   // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
    } else if(type == AST_LEQ) {     // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
    } else if(type == AST_GEQ) {    // OK
        ast_replace_iterator(node->nodes[0]);
        ast_replace_iterator(node->nodes[1]);
    } else if(type == AST_VAR || type == AST_NUM) { // OK
        int var_index = node->sym_index;

        if(var_index == i_index) { // zamiana iteratora na NUMA
            node->sym_index = i_num_index;
            node->type = AST_NUM;
        }
    } else if(type == AST_ARR) { // OK
        ast_replace_iterator(node->nodes[1]);
    }
    return;
}

bool check_num(int index) {
    if(sym_table->symbols[index].type == NUMB) {
        return true;
    }

    return false;
}

unsigned long long get_sym_value(int index) {
    return sym_table->symbols[index].value;
}


void check_extend_tac_o(void) {
    if(program_tac_o->size == program_tac_o->max_size) {
        program_tac_o->max_size *= 2;
        TAC_I* temp = (TAC_I*) realloc(program_tac_o->tac_s, sizeof(TAC_I) * program_tac_o->max_size);
        
        if(temp == NULL) {
            cout << "Memory reallocation failed!" << endl;
            exit(121);
        }
        
        program_tac_o->tac_s = temp;
    }
}

void add_tac_o_ins(tac_type type) {
    check_extend_tac_o();
    program_tac_o->tac_s[program_tac_o->size].type = type;
    program_tac_o->tac_s[program_tac_o->size].size = 0;
    program_tac_o->tac_s[program_tac_o->size].b_index = -1;
    program_tac_o->size++;
}

void add_ins_o_index(int index_1, int index_2) {
    int temp = program_tac_o->tac_s[program_tac_o->size-1].size;
    program_tac_o->tac_s[program_tac_o->size-1].indexes[temp][0] = index_1;
    program_tac_o->tac_s[program_tac_o->size-1].indexes[temp][1] = index_2;
    program_tac_o->tac_s[program_tac_o->size-1].size++;
}



// #######################################################################
// #######################################################################
// #######################################################################

//                         OPTIMIZE TAC

// #######################################################################
// #######################################################################
// #######################################################################

void tac_optimize(void) {
    program_tac_o = (TAC_program*) malloc(sizeof(TAC_program));
    
    if(program_tac_o == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(122);
    }
    
    program_tac_o->max_size = program_tac->max_size;
    program_tac_o->size = 0;
    program_tac_o->tac_s = (TAC_I*) malloc(sizeof(TAC_I) * program_tac->max_size);
    
    if(program_tac_o->tac_s == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(123);
    }
    
    for(int i = 0; i < program_tac->size; i++) {
        TAC_I* temp = &program_tac->tac_s[i];
        tac_type type = temp->type;
        
        if(type == TAC_ASSIGN) { // x := y
            bool arg_2_num = check_num(temp->indexes[1][0]);
            
            if(arg_2_num && get_sym_value(temp->indexes[1][0]) == 0) { // x := 0
                add_tac_o_ins(TAC_RESET);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else {
                    add_tac_o_ins(TAC_ASSIGN);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                    add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else if(type == TAC_ADD) {
            bool arg_1_num = check_num(temp->indexes[1][0]);
            bool arg_2_num = check_num(temp->indexes[2][0]);
            
            if(arg_1_num && arg_2_num) { // x = num + num
                unsigned long long max_testing = ULLONG_MAX;
                max_testing -= get_sym_value(temp->indexes[1][0]);

                if(max_testing >= get_sym_value(temp->indexes[2][0])) {
                    unsigned long long value = get_sym_value(temp->indexes[1][0]) + get_sym_value(temp->indexes[2][0]);
                    int num_len = (int) snprintf(NULL, 0, "%llu", value);
                    char* temp_name = (char*) malloc(num_len + 1);
                    sprintf(temp_name, "%llu", value);
                    temp->indexes[1][0] = add_num_symbol(temp_name);
                    add_tac_o_ins(TAC_ASSIGN);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[1][0], -1);
                    free(temp_name);
                } else {
                    add_tac_o_ins(TAC_ADD);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                    add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
                }
                
            } else if(arg_1_num && get_sym_value(temp->indexes[1][0]) == 0) {  // x = 0 + y
                if(!(temp->indexes[0][0] == temp->indexes[2][0] && temp->indexes[0][1] == temp->indexes[2][1])) { // jezeli x = 0 + x to pomijamy
                    add_tac_o_ins(TAC_ASSIGN);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
                }
            } else if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 0) {  // x = y + 0
                if(!(temp->indexes[0][0] == temp->indexes[1][0] && temp->indexes[0][1] == temp->indexes[1][1])) { // jezeli x = x + 0 to pomijamy
                    add_tac_o_ins(TAC_ASSIGN);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[1][0], -1);
                }
            } else if(!arg_1_num && arg_2_num && get_sym_value(temp->indexes[2][0]) < 5 && temp->indexes[0][0] == temp->indexes[1][0]
                        && temp->indexes[0][1] == temp->indexes[1][1]) {        // x = x + a, gdzie a < 5 zamiana na INC
                int temp_2 = ((int) get_sym_value(temp->indexes[2][0])) - 1;
                add_tac_o_ins(TAC_INC);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                
                for(int j = 0; j < temp_2; j++) {
                    add_tac_o_ins(TAC_INC);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                }
            } else if(arg_1_num && !arg_2_num && get_sym_value(temp->indexes[1][0]) < 5 && temp->indexes[0][0] == temp->indexes[2][0]
                        && temp->indexes[0][1] == temp->indexes[2][1]) {        // x = a + x, gdzie a < 5 zamiana na INC
                int temp_2 = ((int) get_sym_value(temp->indexes[1][0])) - 1;
                add_tac_o_ins(TAC_INC);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                
                for(int j = 0; j < temp_2; j++) {
                    add_tac_o_ins(TAC_INC);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                }
            } else {
                add_tac_o_ins(TAC_ADD);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else if(type == TAC_SUB) {
            bool arg_1_num = check_num(temp->indexes[1][0]);
            bool arg_2_num = check_num(temp->indexes[2][0]);
            
            if(arg_1_num && arg_2_num) { // x = num - num
                unsigned long long arg_1_value = get_sym_value(temp->indexes[1][0]);
                unsigned long long arg_2_value = get_sym_value(temp->indexes[2][0]);
                
                if(arg_1_value <= arg_2_value) { // zeruje sie
                    add_tac_o_ins(TAC_RESET);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                } else {    // jakas liczba wychodzi wieksza od 0
                    unsigned long long value = arg_1_value - arg_2_value;
                    int num_len = (int) snprintf(NULL, 0, "%llu", value);
                    char* temp_name = (char*) malloc(num_len + 1);
                    sprintf(temp_name, "%llu", value);
                    temp->indexes[1][0] = add_num_symbol(temp_name);
                    add_tac_o_ins(TAC_ASSIGN);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[1][0], -1);
                    free(temp_name);
                }
                
            } else if(arg_1_num && get_sym_value(temp->indexes[1][0]) == 0) { // x = 0 - y = 0
                add_tac_o_ins(TAC_RESET);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 0) { // x = y - 0 = y
                if(!(temp->indexes[0][0] == temp->indexes[1][0] && temp->indexes[0][1] == temp->indexes[1][1])) { // jezeli x = x - 0 to pomijamy
                    add_tac_o_ins(TAC_ASSIGN);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                }
            } else if(!arg_1_num && !arg_2_num && temp->indexes[1][0] == temp->indexes[2][0] && temp->indexes[1][1] == temp->indexes[2][1]) { // x = y - y = 0
                add_tac_o_ins(TAC_RESET);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(!arg_1_num && arg_2_num && get_sym_value(temp->indexes[2][0]) < 5 && temp->indexes[0][0] == temp->indexes[1][0]
                        && temp->indexes[0][1] == temp->indexes[1][1]) {        // x = x - a, gdzie a < 5 zamiana na DEC
                int temp_2 = ((int) get_sym_value(temp->indexes[2][0])) - 1;
                add_tac_o_ins(TAC_DEC);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                
                for(int j = 0; j < temp_2; j++) {
                    add_tac_o_ins(TAC_DEC);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                }
            } else {
                add_tac_o_ins(TAC_SUB);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else if(type == TAC_MUL) {
            bool arg_1_num = check_num(temp->indexes[1][0]);
            bool arg_2_num = check_num(temp->indexes[2][0]);
            
            if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 1) { // x = y * 1
                if(!(temp->indexes[0][0] == temp->indexes[1][0] && temp->indexes[0][1] == temp->indexes[1][1])) { // jezeli x = x * 1 to pomijamy
                    add_tac_o_ins(TAC_ASSIGN);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                }
            } else if(arg_1_num && get_sym_value(temp->indexes[1][0]) == 1) { // x = 1 * y
                if(!(temp->indexes[0][0] == temp->indexes[2][0] && temp->indexes[0][1] == temp->indexes[2][1])) { // jezeli x = 1 * x  to pomijamy
                    add_tac_o_ins(TAC_ASSIGN);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
                }
            } else if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 0) { // x = y * 0
                add_tac_o_ins(TAC_RESET);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_1_num && get_sym_value(temp->indexes[1][0]) == 0) { // x = 0 * y
                add_tac_o_ins(TAC_RESET);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_1_num && get_sym_value(temp->indexes[1][0]) == 2) { // x = 2 * y
                if(temp->indexes[0][0] == temp->indexes[2][0] && temp->indexes[0][1] == temp->indexes[2][1]) { // jezeli x = 2 * x  to
                    add_tac_o_ins(TAC_SHL);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                } else {
                    add_tac_o_ins(TAC_ADD);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
                    add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
                }
            } else if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 2) { // x = y * 2
                if(temp->indexes[0][0] == temp->indexes[1][0] && temp->indexes[0][1] == temp->indexes[1][1]) { // jezeli x = x * 2 to
                    add_tac_o_ins(TAC_SHL);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                } else {
                    add_tac_o_ins(TAC_ADD);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                    add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                }
            } else if(arg_1_num && arg_2_num) {
                unsigned long long arg_1_value = get_sym_value(temp->indexes[1][0]);
                unsigned long long arg_2_value = get_sym_value(temp->indexes[2][0]);
                
                if(arg_1_value < (ULLONG_MAX / arg_2_value)) { // wtedy zmiesci sie w ull
                    unsigned long long value = arg_1_value * arg_2_value;
                    int num_len = (int) snprintf(NULL, 0, "%llu", value);
                    char* temp_name = (char*) malloc(num_len + 1);
                    sprintf(temp_name, "%llu", value);
                    add_tac_o_ins(TAC_ASSIGN);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(add_num_symbol(temp_name), -1);
                    free(temp_name);
                }
            } else {
                add_tac_o_ins(TAC_MUL);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else if(type == TAC_DIV) {
            bool arg_1_num = check_num(temp->indexes[1][0]);
            bool arg_2_num = check_num(temp->indexes[2][0]);
            
            if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 0) { // x = y / 0 to wynik x = 0
                add_tac_o_ins(TAC_RESET);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_1_num && get_sym_value(temp->indexes[1][0]) == 0) { // x = 0 / y to wynik x = 0
                add_tac_o_ins(TAC_RESET);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 1) { // x = y / 1 to wynik x = y
                if(!(temp->indexes[0][0] == temp->indexes[1][0] && temp->indexes[0][1] == temp->indexes[1][1])) { // jezeli x = x / 1  to pomijamy
                    add_tac_o_ins(TAC_ASSIGN);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                }
            } else if (!arg_1_num && arg_2_num && get_sym_value(temp->indexes[2][0]) == 2) { // x = y / 2 to SHR
                if(temp->indexes[0][0] == temp->indexes[1][0] && temp->indexes[0][1] == temp->indexes[1][1]) { // jezeli x = x / 2  to
                    add_tac_o_ins(TAC_SHR);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                } else {
                    add_tac_o_ins(TAC_DIV);
                    add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                    add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                    add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
                }
            } else if(arg_1_num && arg_2_num) { // x = num / num to wynik x = num
                unsigned long long arg_1_value = get_sym_value(temp->indexes[1][0]);
                unsigned long long arg_2_value = get_sym_value(temp->indexes[2][0]);
                
                unsigned long long value = arg_1_value / arg_2_value;
                int num_len = (int) snprintf(NULL, 0, "%llu", value);
                char* temp_name = (char*) malloc(num_len + 1);
                sprintf(temp_name, "%llu", value);
                add_tac_o_ins(TAC_ASSIGN);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(add_num_symbol(temp_name), -1);
                free(temp_name);
            } else {
                add_tac_o_ins(TAC_DIV);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else if(type == TAC_MOD) {
            bool arg_1_num = check_num(temp->indexes[1][0]);
            bool arg_2_num = check_num(temp->indexes[2][0]);
            
            if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 0) { // x = y % 0 to wynik x = 0
                add_tac_o_ins(TAC_RESET);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_1_num && get_sym_value(temp->indexes[1][0]) == 0) { // x = 0 % y to wynik x = 0
                add_tac_o_ins(TAC_RESET);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 1) { // x = y % 1 to wynik x = 0
                add_tac_o_ins(TAC_RESET);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_1_num && arg_2_num) {
                unsigned long long arg_1_value = get_sym_value(temp->indexes[1][0]);
                unsigned long long arg_2_value = get_sym_value(temp->indexes[2][0]);
                
                unsigned long long value = arg_1_value % arg_2_value;
                int num_len = (int) snprintf(NULL, 0, "%llu", value);
                char* temp_name = (char*) malloc(num_len + 1);
                sprintf(temp_name, "%llu", value);
                add_tac_o_ins(TAC_ASSIGN);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(add_num_symbol(temp_name), -1);
                free(temp_name);
            } else {
                add_tac_o_ins(TAC_MOD);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else if(type == TAC_JEQ) {
            bool arg_1_num = check_num(temp->indexes[1][0]);
            bool arg_2_num = check_num(temp->indexes[2][0]);
            
            if(arg_1_num && arg_2_num && get_sym_value(temp->indexes[1][0]) == get_sym_value(temp->indexes[2][0])) { // JEQ num1 num2 gdzie num1 == num2 to JUMP
                add_tac_o_ins(TAC_JUMP);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_1_num && get_sym_value(temp->indexes[1][0]) == 0) { // JEQ 0 x to JZERO x
                add_tac_o_ins(TAC_JZERO);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            } else if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 0) { // JEQ x 0 to JZERO x
                add_tac_o_ins(TAC_JZERO);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
            } else {
                add_tac_o_ins(TAC_JEQ);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else if(type == TAC_JNEQ) {
            bool arg_1_num = check_num(temp->indexes[1][0]);
            bool arg_2_num = check_num(temp->indexes[2][0]);
            
            if(arg_1_num && arg_2_num && get_sym_value(temp->indexes[1][0]) != get_sym_value(temp->indexes[2][0])) { // JNEQ num1 num2 gdzie num1 != num2 to JUMP
                add_tac_o_ins(TAC_JUMP);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else {
                add_tac_o_ins(TAC_JNEQ);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else if(type == TAC_JLT) {
            bool arg_1_num = check_num(temp->indexes[1][0]);
            bool arg_2_num = check_num(temp->indexes[2][0]);
            
            if(arg_1_num && arg_2_num && get_sym_value(temp->indexes[1][0]) < get_sym_value(temp->indexes[2][0])) { // JLT num1 num2 gdzie num1 < num2 to JUMP
                add_tac_o_ins(TAC_JUMP);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else {
                add_tac_o_ins(TAC_JLT);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else if(type == TAC_JGT) {
            bool arg_1_num = check_num(temp->indexes[1][0]);
            bool arg_2_num = check_num(temp->indexes[2][0]);
            
            if(arg_1_num && arg_2_num && get_sym_value(temp->indexes[1][0]) > get_sym_value(temp->indexes[2][0])) { // JGT num1 num2 gdzie num1 > num2 to JUMP
                add_tac_o_ins(TAC_JUMP);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else {
                add_tac_o_ins(TAC_JGT);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else if(type == TAC_JLEQ) {
            bool arg_1_num = check_num(temp->indexes[1][0]);
            bool arg_2_num = check_num(temp->indexes[2][0]);
            
            if(arg_1_num && arg_2_num && get_sym_value(temp->indexes[1][0]) <= get_sym_value(temp->indexes[2][0])) { // JLEQ num1 num2 gdzie num1 <= num2 to JUMP
                add_tac_o_ins(TAC_JUMP);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_1_num && get_sym_value(temp->indexes[1][0]) == 0) { // JLEQ num x gdzie num = 0 to x zawsze spelnia wiec JUMP
                add_tac_o_ins(TAC_JUMP);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 0) { // JLEQ x num gdzie num = 0 to x spelnia gdy jest 0 wiec JZERO
                add_tac_o_ins(TAC_JZERO);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
            } else {
                add_tac_o_ins(TAC_JLEQ);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else if(type == TAC_JGEQ) {
            bool arg_1_num = check_num(temp->indexes[1][0]);
            bool arg_2_num = check_num(temp->indexes[2][0]);
            
            if(arg_1_num && arg_2_num && get_sym_value(temp->indexes[1][0]) >= get_sym_value(temp->indexes[2][0])) { // JGEQ num1 num2 gdzie num1 >= num2 to JUMP
                add_tac_o_ins(TAC_JUMP);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_2_num && get_sym_value(temp->indexes[2][0]) == 0) { // JGEQ x num gdzie num = 0 to x zawsze spelnia wiec JUMP
                add_tac_o_ins(TAC_JUMP);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            } else if(arg_1_num && get_sym_value(temp->indexes[1][0]) == 0) { // JGEQ num x gdzie num = 0 to x spelnia gdzy jest 0 wiec JZERO
                add_tac_o_ins(TAC_JZERO);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            } else {
                add_tac_o_ins(TAC_JGEQ);
                add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
                add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
                add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
            }
        } else {
            add_tac_o_ins(type);
            add_ins_o_index(temp->indexes[0][0], temp->indexes[0][1]);
            add_ins_o_index(temp->indexes[1][0], temp->indexes[1][1]);
            add_ins_o_index(temp->indexes[2][0], temp->indexes[2][1]);
        }
    }
}

void count_blocks() { // NUMERUJE BLOKI W PROG. UWAGA OPTIMIZED
    int counter = 0;
    
    for(int i = 0; i < program_tac_o->size; i++) {
        tac_type temp = program_tac_o->tac_s[i].type;
        
        if(temp == TAC_LABEL || temp == TAC_JUMP || temp == TAC_JZERO || temp == TAC_JEQ
            || temp == TAC_JNEQ || temp == TAC_JLT || temp == TAC_JGT || temp == TAC_JLEQ || temp == TAC_JGEQ) {
            counter++;
        }
        program_tac_o->tac_s[i].b_index = counter;
    }
}





// #######################################################################
// #######################################################################
// #######################################################################

//                         REJESTRY

// #######################################################################
// #######################################################################
// #######################################################################




void init_registers() {
    for(int i = 0; i < 6; i++) {
        reg[i].free = true;
        reg[i].locked = -1;
        reg[i].must_store = -1;
        reg[i].index[0] = -1;
        reg[i].index[1] = -1;
        reg[i].has_val = false;
        reg[i].value = 0;
        reg[i].ins.type = TAC_UNDEFINED;
    }
}


void set_register(int r_index, unsigned long long value) { // OK
    bool has_value = reg[r_index].has_val;
    
    if(has_value && reg[r_index].value == value) {
        return;
    } else if(has_value && reg[r_index].value > value) {
        unsigned long long temp = reg[r_index].value - value;
        
        if(temp < 3) {
            for(unsigned long long i = 0; i < temp; i++) {
                add_rmc_ins(RMC_DEC, r_index, -1, -1);
            }

            reg[r_index].value = value;
            return;
        }
    } else if(has_value && reg[r_index].value < value) {
        unsigned long long temp = value - reg[r_index].value;
        
        if(temp < 3) {
            for(unsigned long long i = 0; i < temp; i++) {
                add_rmc_ins(RMC_INC, r_index, -1, -1);
            }

            reg[r_index].value = value;
            return;
        }
    }
    
    gen_const(r_index, value);
    reg[r_index].has_val = true;
    reg[r_index].value = value;
    return;
}


void gen_const(int index, unsigned long long value) { // OK !!!!!!!!!!!!!!
    add_rmc_ins(RMC_RESET, index, -1, -1); // stala to 0

    if(value == 0) {
        return;
    }
    
    add_rmc_ins(RMC_INC, index, -1, -1); // stala to 1

    if(value == 1) {
        return;
    }
    
    int temp[70];
    int i = 0;
    
    while(value != 0) {
        int r = value % 2;
        temp[i] = r;
        value /= 2;
        i++;
    }

    i -= 2;
    
    for(int j = i; j >= 0; j--) {
        add_rmc_ins(RMC_SHL, index, -1, -1); // stala = stala * 2
        
        if(temp[j] == 1) {
            add_rmc_ins(RMC_INC, index, -1, -1); // jeden bit na lsb stalej
        }
    }
    return;    
}



void reset_regs() {   //   RESETOWANIE REJESTROW WSZYSTKICH // OK !!!!!!!!!!!!!!

    for(int i = 0; i < 6; i++) {
        if(!reg[i].free && reg[i].index[1] != -1) {
            for(int j = 0; j < 6; j++) {
                if(reg[i].index[1] == reg[j].index[0]) {
                    store_reg(i);
                }
            }
        }
    }

    for(int i = 0; i < 6; i++) {
        if(!reg[i].free && reg[i].index[1] != -1) {
            store_reg(i);
        }
    }

    for(int i = 0; i < 6; i++) {
        if(!reg[i].free) {
            store_reg(i);
        }
    }

    for(int i = 0; i < 6; i++) {
        reg[i].free = true;
        reg[i].locked = -1;
        reg[i].must_store = false;
        reg[i].index[0] = -1;
        reg[i].index[1] = -1;
        reg[i].has_val = false;
        reg[i].value = -1;
        reg[i].ins.type = TAC_UNDEFINED;
    }
    return;
}


int check_reg_filled(int index_1, int index_2) {
    for(int i = 0; i < 6; i++) {
        if(reg[i].locked != 1 && reg[i].index[0] == index_1 && reg[i].index[1] == index_2) {
            reg[i].locked = 1;
            return i;
        }
    }
    return -1;
}


int check_filled_reg_value(unsigned long long value) {
    for(int i = 0; i < 6; i++) {
        if(reg[i].has_val && reg[i].value == value) {
            return i;
        }
    }
    return -1;
}



bool store_reg(int index) {
    reg[index].locked = 1;
    
    if(!reg[index].must_store || check_num(reg[index].index[0])) { // nie wymagane zapisanie lub stala
        reg[index].free = true;
        return true;
    } else if(reg[index].index[1] == -1) { // to jest zmienna
        int temp_1 = get_address_filled_reg(reg[index].index[0], -1); // zwraca rej wypelniony adresem zmiennej

        add_rmc_ins(RMC_STORE, index, temp_1, -1); // zapisz wartosc rejestru index do pamieci o adresie temp_1
        reg[index].free = false;
        reg[index].locked = 0;
        reg[index].must_store = false;
        return true;
    } else if(check_num(reg[index].index[1])) { // tab o num indexie
        int temp_1 = get_address_filled_reg(reg[index].index[0], reg[index].index[1]); // zwraca rej wypelniony adresem zmiennej typu ARR[NUM]

        add_rmc_ins(RMC_STORE, index, temp_1, -1); // zapisz wartosc rejestru index do pamieci o adresie temp_1
        reg[index].free = false;
        reg[index].locked = 0;
        reg[index].must_store = false;
        return true;
    } else { // PRZYPADEK ARR[VAR]
        int temp_1 = get_address_filled_reg(reg[index].index[0], reg[index].index[1]); // zwraca rej wypelniony adresem zmiennej typu ARR[VAR]
        add_rmc_ins(RMC_STORE, index, temp_1, -1); // zapisz wartosc rejestru index do pamieci o adresie temp_1
        reg[index].free = false;
        reg[index].locked = 0;
        reg[index].must_store = false;
        return true;
    }
    reg[index].locked = 0;
    return false;
}

int find_good_reg(void) {
    int temp = find_f_s_reg();

    if(temp >= 0) {
        return temp;
    }
    
    for(int i = 0; i < 6; i++) {
        if(reg[i].locked == 0) { // jezeli nie jest zablokowany i moze zostac zwolniony 
            if(store_reg(i)) { // jezeli jest zwolniony
                reg[i].free = false;
                reg[i].locked = 1;
                reg[i].must_store = false;
                reg[i].index[0] = -1;
                reg[i].index[1] = -1;
                reg[i].has_val = false;
                reg[i].value = -1;
                reg[i].ins.type = TAC_UNDEFINED;
                return i;
            }
        }
    }
    
    return -1;
}

int find_f_s_reg(void) {
    for(int i = 0; i < 6; i++) { // SZUKANIE CALKOWICIE WOLNEGO REJESTRU
        if(reg[i].free) { // jezeli jest wolny 
            reg[i].free = false;
            reg[i].locked = 1;
            reg[i].must_store = false;
            reg[i].index[0] = -1;
            reg[i].index[1] = -1;
            reg[i].has_val = false;
            reg[i].value = -1;
            reg[i].ins.type = TAC_UNDEFINED;
            return i;
        }
    }
    
    for(int i = 0; i < 6; i++) { // SZUKANIE REJESTRU NIEZABLOKOWANEGO, KTOREGO NIE TRZEBA ZAPISAC
        if(reg[i].locked == 0 && !reg[i].must_store && reg[i].ins.type == TAC_UNDEFINED) { 
            reg[i].free = false;
            reg[i].locked = 1;
            reg[i].must_store = false;
            reg[i].index[0] = -1;
            reg[i].index[1] = -1;
            reg[i].has_val = false;
            reg[i].value = -1;
            reg[i].ins.type = TAC_UNDEFINED;
            return i;
        }
    }
    
    for(int i = 0; i < 6; i++) { // SZUKANIE REJESTRU NIEZABLOKOWANEGO, ZAJETEGO PRZEZ ZMIENNA VAR
        if(reg[i].locked == 0 && reg[i].index[1] == -1) {
            if(store_reg(i)) { // jezeli udalo sie zwolnic lub nie bylo potrzeby zapisania
                reg[i].free = false;
                reg[i].locked = 1;
                reg[i].must_store = false;
                reg[i].index[0] = -1;
                reg[i].index[1] = -1;
                reg[i].has_val = false;
                reg[i].value = -1;
                reg[i].ins.type = TAC_UNDEFINED;
                return i;
            }
        }
    }
    
    for(int i = 0; i < 6; i++) { // SZUKANIE REJESTRU NIEZABLOKOWANEGO, KTOREGO NIE TRZEBA ZAPISAC
        if(reg[i].locked == 0 && !reg[i].must_store) { 
            reg[i].free = false;
            reg[i].locked = 1;
            reg[i].must_store = false;
            reg[i].index[0] = -1;
            reg[i].index[1] = -1;
            reg[i].has_val = false;
            reg[i].value = -1;
            reg[i].ins.type = TAC_UNDEFINED;
            return i;
        }
    }
    return -1;
}


int get_filled_reg(int index_1, int index_2) {  //  ZNAJDUJE I WYPELNIA REJESTR DLA DANEYCH INDEKSÓW SYMBOLI !!!!!!!!!!!!!!!!!!!!!!!!!!!!!
    int temp_1 = check_reg_filled(index_1, index_2);

    if(temp_1 >= 0) {
        return temp_1;
    }
    
    if(check_num(index_1)) { // stala num do byle jakiego rejestru 
        temp_1 = find_good_reg();

        if(temp_1 < 0) {
            cout << "Free register not found! Fatal error O_O" << endl;
            exit(123);
        }

        set_register(temp_1, get_sym_value(index_1));
    } else if(index_2 == -1) { // zmienna x do byle jakiego rejestru
        temp_1 = find_good_reg();

        if(temp_1 < 0) {
            cout << "Free register not found! Fatal error O_O" << endl;
            exit(123);
        }

        int temp_2 = check_filled_reg_value(get_mem_address(index_1));
        
        if(temp_2 < 0) {
            set_register(temp_1, get_mem_address(index_1));
            add_rmc_ins(RMC_LOAD, temp_1, temp_1, -1);
            reg[temp_1].free = false;
            reg[temp_1].must_store = false;
            reg[temp_1].has_val = false;
            reg[temp_1].value = -1;
            reg[temp_1].index[0] = -1;
            reg[temp_1].index[1] = -1;
        } else {
            add_rmc_ins(RMC_LOAD, temp_1, temp_2, -1);
        }
        reg[temp_1].free = false;
        reg[temp_1].must_store = false;
        reg[temp_1].has_val = false;
        reg[temp_1].value = -1;
        reg[temp_1].index[0] = -1;
        reg[temp_1].index[1] = -1;
        
    } else { // tablica na pewno 
        for(int i = 0; i < 6; i++) { // SZUKANIE REJESTRU NIEZABLOKOWANEGO, ZAJETEGO PRZEZ ZMIENNA ARR[ COS ]
            if(reg[i].locked == 0 && reg[i].index[0] == index_1) {
                if(store_reg(i)) { // jezeli udalo sie zwolnic lub nie bylo potrzeby zapisania
                    reg[i].free = false;
                    reg[i].locked = 1;
                    reg[i].must_store = false;
                    reg[i].index[0] = -1;
                    reg[i].index[1] = -1;
                    reg[i].has_val = false;
                    reg[i].value = -1;
                    reg[i].ins.type = TAC_UNDEFINED;
                }
            }
        }
        
        if(check_num(index_2)) { // tablica tab[num]   OK
            temp_1 = find_good_reg();

            if(temp_1 < 0) {
                cout << "Free register not found! Fatal error O_O" << endl;
                exit(123);
            }

            int temp_2 = check_filled_reg_value(get_mem_arr_address(index_1, get_sym_value(index_2)));
        
            if(temp_2 < 0) {
                set_register(temp_1, get_mem_arr_address(index_1, get_sym_value(index_2)));
                add_rmc_ins(RMC_LOAD, temp_1, temp_1, -1);
            } else {
                add_rmc_ins(RMC_LOAD, temp_1, temp_2, -1);
            }
            reg[temp_1].has_val = false;
            reg[temp_1].value = -1;
        } else { // tablica tab[var]
            temp_1 = get_filled_reg(index_2, -1); // tutaj w reg juz siedzi ta zmienna

            if(temp_1 < 0) {
                cout << "Free register not found! Fatal error O_O" << endl;
                exit(123);
            }

            long long temp_2 = sym_table->symbols[index_1].mem_i - sym_table->symbols[index_1].offset;

            if(temp_2 >= 0) {
                if(temp_2 < 5) {
                    forget_reg(index_2, -1);

                    for(int i = 0; i < temp_2; i++) {
                        add_rmc_ins(RMC_INC, temp_1, -1, -1); // zwieksza jesli bylo <5 zwiekszen
                    }
                } else {
                    int temp_3 = check_filled_reg_value(temp_2); // spr czy juz jest ta wartosc w jakims rejestrze
        
                    if(temp_3 < 0) { // jak nie ma to szuka nowego rej i do niego ustawia wartosc
                        temp_3 = find_good_reg();

                        if(temp_3 < 0) {
                            cout << "Free register not found! Fatal error O_O" << endl;
                            exit(123);
                        }
                    
                        set_register(temp_3, temp_2);    
                    }
                    add_rmc_ins(RMC_ADD, temp_1, temp_3, -1); // w obu przypadkach dodaje na koncu
                    reg[temp_3].free = true;
                    reg[temp_3].must_store = false;
                    reg[temp_3].has_val = false;
                    reg[temp_3].value = -1;
                    reg[temp_3].index[0] = -1;
                    reg[temp_3].index[1] = -1;
                }
            } else {
                if(temp_2 > -5) {
                    forget_reg(index_2, -1);

                    for(int i = 0; i > temp_2; i--) {
                        add_rmc_ins(RMC_DEC, temp_1, -1, -1); // zmniejsza jesli bylo <5 zmniejszen
                    }
                } else {
                    int temp_3 = check_filled_reg_value(sym_table->symbols[index_1].mem_i); // spr czy juz jest ta wartosc w jakims rejestrze
        
                    if(temp_3 < 0) { // jak nie ma to szuka nowego rej i do niego ustawia wartosc
                        temp_3 = find_good_reg();

                        if(temp_3 < 0) {
                            cout << "Free register not found! Fatal error O_O" << endl;
                            exit(123);
                        }
                    
                        set_register(temp_3, sym_table->symbols[index_1].mem_i);    
                    }
                    add_rmc_ins(RMC_ADD, temp_1, temp_3, -1);
                    set_register(temp_3, sym_table->symbols[index_1].offset);
                    add_rmc_ins(RMC_SUB, temp_1, temp_3, -1);
                    reg[temp_3].free = true;
                    reg[temp_3].must_store = false;
                    reg[temp_3].has_val = false;
                    reg[temp_3].value = -1;
                    reg[temp_3].index[0] = -1;
                    reg[temp_3].index[1] = -1;
                }
            }
            add_rmc_ins(RMC_LOAD, temp_1, temp_1, -1); // temp1 to adres w pamieci, temp1 to wynik
            
            reg[temp_1].free = false;
            reg[temp_1].must_store = false;
            reg[temp_1].has_val = false;
            reg[temp_1].value = -1;
            reg[temp_1].index[0] = -1;
            reg[temp_1].index[1] = -1;
        }
    }
    
    reg[temp_1].index[0] = index_1;
    reg[temp_1].index[1] = index_2;
    return temp_1;
}



int get_address_filled_reg(int i_1, int i_2) { // ZWRACA REJESTR WYPELNIONY ADRESEM DANEGO SYMBOLU
    int temp = -1;
    
    if(i_2 == -1) { // to zmienna lub stala
        temp = check_filled_reg_value(get_mem_address(i_1));
        
        if(temp < 0) { // nie znalazlo reg o takiej wartosci
            temp = find_good_reg(); // jesli nie znalazlo to szuka dobrego rej do uzytku

            if(temp < 0) {
                cout << "Free register not found! Fatal error O_O" << endl;
                exit(123);
            }
            set_register(temp, get_mem_address(i_1));
        }
        return temp;
    } else { // to tablica jakas
        if(check_num(i_2)) { // to tablica postaci ARR[NUM]
            temp = check_filled_reg_value(get_mem_arr_address(i_1, get_sym_value(i_2)));
        
            if(temp < 0) { // nie znalazlo reg o takiej wartosci
                temp = find_good_reg(); // jesli nie znalazlo to szuka dobrego rej do uzytku

                if(temp < 0) {
                    cout << "Free register not found! Fatal error O_O" << endl;
                    exit(123);
                }
            set_register(temp, get_mem_arr_address(i_1, get_sym_value(i_2)));
            }
            return temp;
        } else { // to tablica postaci ARR[VAR]
            int temp = get_filled_reg(i_2, -1); // tutaj w reg juz siedzi ta zmienna

            if(temp < 0) {
                cout << "Free register not found! Fatal error O_O" << endl;
                exit(123);
            }
            
            long long temp_2 = sym_table->symbols[i_1].mem_i - sym_table->symbols[i_1].offset; // wartosc do ktorej dodaje sie zmienna z temp

            if(temp_2 >= 0) {
                if(temp_2 < 5) {
                    forget_reg(i_2, -1);

                    for(int i = 0; i < temp_2; i++) {
                        add_rmc_ins(RMC_INC, temp, -1, -1); // zwieksza jesli bylo <5 zwiekszen
                    }
                } else {
                    int temp_3 = check_filled_reg_value(temp_2); // spr czy juz jest ta wartosc w jakims rejestrze
        
                    if(temp_3 < 0) { // jak nie ma to szuka nowego rej i do niego ustawia wartosc
                        temp_3 = find_good_reg();

                        if(temp_3 < 0) {
                            cout << "Free register not found! Fatal error O_O" << endl;
                            exit(123);
                        }
                    
                        set_register(temp_3, temp_2);    
                    }
                    add_rmc_ins(RMC_ADD, temp, temp_3, -1); // w obu przypadkach dodaje na koncu
                    reg[temp_3].free = true;
                    reg[temp_3].must_store = false;
                    reg[temp_3].has_val = false;
                    reg[temp_3].value = -1;
                    reg[temp_3].index[0] = -1;
                    reg[temp_3].index[1] = -1;
                }
            } else {
                if(temp_2 > -5) {
                    forget_reg(i_2, -1);

                    for(int i = 0; i > temp_2; i--) {
                        add_rmc_ins(RMC_DEC, temp, -1, -1); // zwieksza jesli bylo <5 zwiekszen
                    }
                } else {
                    int temp_3 = check_filled_reg_value(sym_table->symbols[i_1].mem_i); // spr czy juz jest ta wartosc w jakims rejestrze
        
                    if(temp_3 < 0) { // jak nie ma to szuka nowego rej i do niego ustawia wartosc
                        temp_3 = find_good_reg();

                        if(temp_3 < 0) {
                            cout << "Free register not found! Fatal error O_O" << endl;
                            exit(123);
                        }
                    
                        set_register(temp_3, sym_table->symbols[i_1].mem_i);    
                    }

                    add_rmc_ins(RMC_ADD, temp, temp_3, -1);
                    set_register(temp_3, sym_table->symbols[i_1].offset);
                    add_rmc_ins(RMC_SUB, temp, temp_3, -1);
                    reg[temp_3].free = true;
                    reg[temp_3].must_store = false;
                    reg[temp_3].has_val = false;
                    reg[temp_3].value = -1;
                    reg[temp_3].index[0] = -1;
                    reg[temp_3].index[1] = -1;
                }
            }
            return temp;
        }
    }
}


void forget_reg(int index_1, int index_2) {
    for(int i = 0; i < 6; i++) {
        if(reg[i].index[0] == index_1 && reg[i].index[1] == index_2) {
            reg[i].free = true;
            reg[i].locked = -1;
            reg[i].must_store = false;
            reg[i].index[0] = -1;
            reg[i].index[1] = -1;
            reg[i].has_val = false;
            reg[i].value = -1;
            reg[i].ins.type = TAC_UNDEFINED;
        }
    }
    return;
}

void reg_arr_var_store(int index) { // jesli zmienna typu ARR[VAR] musi zostal zapisana w memory
    for(int i = 0; i < 6; i++) {
        if(reg[i].index[1] == index) {
            store_reg(i);
            reg[i].free = true;
            reg[i].locked = -1;
            reg[i].must_store = false;
            reg[i].index[0] = -1;
            reg[i].index[1] = -1;
            reg[i].has_val = false;
            reg[i].value = -1;
            reg[i].ins.type = TAC_UNDEFINED;
        }
    }
    return;
}


// #######################################################################
// #######################################################################
// #######################################################################

//                         TAC_OPTIMIZED TO RMC

// #######################################################################
// #######################################################################
// #######################################################################


void init_RMC_program(void) {
    program_rmc = (RMC_program*) malloc(sizeof(RMC_program));
    
    if(program_rmc == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(124);
    }
    
    program_rmc->max_size = RMC_MAX_SIZE;
    program_rmc->size = 0;
    program_rmc->rmc_s = (RMC_I*) malloc(sizeof(RMC_I) * RMC_MAX_SIZE);
    
    if(program_rmc->rmc_s == NULL) {
        cout << "Memory allocation failed!" << endl;
        exit(125);
    }
}


void check_extend_rmc(void) {
    if(program_rmc->size == program_rmc->max_size) {
        program_rmc->max_size *= 2;
        RMC_I* temp = (RMC_I*) realloc(program_rmc->rmc_s, sizeof(RMC_I) * program_rmc->max_size);
        
        if(temp == NULL) {
            cout << "Memory reallocation failed!" << endl;
            exit(126);
        }
        
        program_rmc->rmc_s = temp;
    }
}


void add_rmc_ins(rmc_type type, int i_1, int i_2, int j_dest) {
    check_extend_rmc();
    
    program_rmc->rmc_s[program_rmc->size].type = type;
    program_rmc->rmc_s[program_rmc->size].index[0] = i_1;
    program_rmc->rmc_s[program_rmc->size].index[1] = i_2;
    program_rmc->rmc_s[program_rmc->size].jump_dest = j_dest;
    program_rmc->size++;
}


void tac_to_rmc(void) {
    int regs[6];
    int lab[10];
    int l_counter = l_index;
    int p_block = 0;
    int c_block = -1;
    
    for(int i = 0; i < program_tac_o->size; i++) {
        c_block = program_tac_o->tac_s[i].b_index;
        
        if(p_block != c_block && i > 0) {
            reset_regs();
            p_block = c_block;
        }
        
        tac_type type = program_tac_o->tac_s[i].type; // tu bierze optimized
        TAC_I temp = program_tac_o->tac_s[i];
        
        if(type == TAC_LABEL) {
            add_rmc_ins(RMC_LABEL, -1, -1, temp.indexes[0][0]);
            
        } else if(type == TAC_ASSIGN) {
            reset_regs();
            regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // REJESTR z tym co jest po prawej str:   PID := RIGHT
            reg[regs[0]].locked = 1;
            regs[1] = get_address_filled_reg(temp.indexes[0][0], temp.indexes[0][1]); // REJESTR z adresem PID'a po lewej
            
            add_rmc_ins(RMC_STORE, regs[0], regs[1], -1); // umieszcza wartosc RIGHT w pamieci tego PID'a
            reg[regs[0]].free = true;
            reg[regs[0]].must_store = false;
            reg[regs[0]].locked = 0;
            reg[regs[0]].has_val = false;
            reg[regs[0]].value = -1;
            reg[regs[0]].index[0] = -1;
            reg[regs[0]].index[1] = -1;
            reg[regs[1]].free = true;
            reg[regs[1]].must_store = false;
            reg[regs[1]].has_val = false;
            reg[regs[1]].value = -1;
            reg[regs[1]].locked = 0;
            reg[regs[1]].index[0] = -1;
            reg[regs[1]].index[1] = -1;
            reset_regs();
            
        } else if(type == TAC_JUMP) {
            add_rmc_ins(RMC_JUMP, -1, -1, temp.indexes[0][0]); // umieszcza wartosc labela do skoku w instrukcji
            
        } else if(type == TAC_JZERO) {
            reset_regs();
            regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // REJESTR z tym PIDEM:   JZERO PID
            add_rmc_ins(RMC_JZERO, regs[0], -1, temp.indexes[0][0]); // umieszcza wartosc labela do skoku w instrukcji
            reg[regs[0]].free = false;
            reg[regs[0]].must_store = false;
            reg[regs[0]].locked = 0;
            reg[regs[0]].index[0] = temp.indexes[1][0];
            reg[regs[0]].index[1] = temp.indexes[1][1];
            reset_regs();
            
        } else if(type == TAC_JEQ) {
            reset_regs();
            lab[0] = l_counter;
            l_counter++;
            lab[1] = l_counter;
            l_counter++;
            regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // REJESTR z tym PIDEM 1:   JEQ PID1 PID2
            reg[regs[0]].locked = 1;
            regs[1] = get_filled_reg(temp.indexes[2][0], temp.indexes[2][1]); // REJESTR z tym PIDEM 2:   JEQ PID1 PID2
            reg[regs[1]].locked = 1;
            regs[2] = find_good_reg(); // REJESTR z byle czym
            add_rmc_ins(RMC_RESET, regs[2], -1, -1); // ustawia rej na 0
            add_rmc_ins(RMC_ADD, regs[2], regs[0], -1); // umieszcza wartosc pierwszej liczby w temp rejestrze
            add_rmc_ins(RMC_SUB, regs[2], regs[1], -1); // pierwsze odejmowanie
            add_rmc_ins(RMC_JZERO, regs[2], -1, lab[0]); // skacze do drugiego sprawdzenia jesli pierwsze bylo ok
            add_rmc_ins(RMC_JUMP, -1, -1, lab[1]); // wychodzi jesli bylo pierwsze zle
            add_rmc_ins(RMC_LABEL, -1, -1, lab[0]); // tu zaczyna sie drugie sprawdzanie
            add_rmc_ins(RMC_RESET, regs[2], -1, -1); // ustawia rej na 0
            add_rmc_ins(RMC_ADD, regs[2], regs[1], -1); // umieszcza wartosc drugiej liczby w temp rejestrze
            add_rmc_ins(RMC_SUB, regs[2], regs[0], -1); // drugie odejmowanie
            add_rmc_ins(RMC_JZERO, regs[2], -1, temp.indexes[0][0]); // udalo sie to wykonuje JEQ 
            add_rmc_ins(RMC_LABEL, -1, -1, lab[1]);
            
            reg[regs[0]].free = false;
            reg[regs[0]].must_store = false;
            reg[regs[0]].locked = 0;
            reg[regs[1]].free = false;
            reg[regs[1]].must_store = false;
            reg[regs[1]].locked = 0;
            reg[regs[2]].free = true;
            reg[regs[2]].must_store = false;
            reg[regs[2]].locked = 0;
            reg[regs[2]].index[0] = -1;
            reg[regs[2]].index[1] = -1;
            reset_regs();
            
        } else if(type == TAC_JNEQ) {
            reset_regs();
            lab[0] = l_counter;
            l_counter++;
            lab[1] = l_counter;
            l_counter++;
            regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // REJESTR z tym PIDEM 1:   JNEQ PID1 PID2
            reg[regs[0]].locked = 1;
            regs[1] = get_filled_reg(temp.indexes[2][0], temp.indexes[2][1]); // REJESTR z tym PIDEM 2:   JNEQ PID1 PID2
            reg[regs[1]].locked = 1;
            regs[2] = find_good_reg(); // REJESTR z byle czym
            add_rmc_ins(RMC_RESET, regs[2], -1, -1); // ustawia rej na 0
            add_rmc_ins(RMC_ADD, regs[2], regs[0], -1); // umieszcza wartosc pierwszej liczby w temp rejestrze
            add_rmc_ins(RMC_SUB, regs[2], regs[1], -1); // pierwsze odejmowanie
            add_rmc_ins(RMC_JZERO, regs[2], -1, lab[0]); // skacze do drugiego sprawdzenia jesli pierwsze bylo zle
            
            add_rmc_ins(RMC_JUMP, -1, -1, temp.indexes[0][0]); // udalo sie jesli bylo pierwsze ok
            add_rmc_ins(RMC_LABEL, -1, -1, lab[0]); // tu zaczyna sie drugie sprawdzanie
            add_rmc_ins(RMC_RESET, regs[2], -1, -1); // ustawia rej na 0
            add_rmc_ins(RMC_ADD, regs[2], regs[1], -1); // umieszcza wartosc drugiej liczby w temp rejestrze
            add_rmc_ins(RMC_SUB, regs[2], regs[0], -1); // drugie odejmowanie
            add_rmc_ins(RMC_JZERO, regs[2], -1, lab[1]); // jesli nadal jest zero to znaczy ze byly rowne
            add_rmc_ins(RMC_JUMP, -1, -1, temp.indexes[0][0]); // udalo sie jesli bylo drugie ok
            add_rmc_ins(RMC_LABEL, -1, -1, lab[1]);
            
            reg[regs[0]].free = false;
            reg[regs[0]].must_store = false;
            reg[regs[0]].locked = 0;
            reg[regs[1]].free = false;
            reg[regs[1]].must_store = false;
            reg[regs[1]].locked = 0;
            reg[regs[2]].free = true;
            reg[regs[2]].must_store = false;
            reg[regs[2]].locked = 0;
            reg[regs[2]].index[0] = -1;
            reg[regs[2]].index[1] = -1;
            reset_regs();
            
        } else if(type == TAC_JLT) {
            reset_regs();
            lab[0] = l_counter;
            l_counter++;
            regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // REJESTR z tym PIDEM 1:   JLT PID1 PID2
            reg[regs[0]].locked = 1;
            regs[1] = get_filled_reg(temp.indexes[2][0], temp.indexes[2][1]); // REJESTR z tym PIDEM 2:   JLT PID1 PID2
            add_rmc_ins(RMC_SUB, regs[1], regs[0], -1); // odejmowanie PID2 - PID 1
            add_rmc_ins(RMC_JZERO, regs[1], -1, lab[0]); // skacze do labela exit jesli bylo zle
            add_rmc_ins(RMC_JUMP, -1, -1, temp.indexes[0][0]); // udalo sie to skacze
            add_rmc_ins(RMC_LABEL, -1, -1, lab[0]); // tu skacze jesli nie jest LT
            
            
            reg[regs[0]].free = false;
            reg[regs[0]].must_store = false;
            reg[regs[0]].locked = 0;
            reg[regs[1]].free = true;
            reg[regs[1]].must_store = false;
            reg[regs[1]].locked = 0;
            reg[regs[1]].index[0] = -1;
            reg[regs[1]].index[1] = -1;
            reset_regs();

        } else if(type == TAC_JGT) {
            reset_regs();
            lab[0] = l_counter;
            l_counter++;
            regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // REJESTR z tym PIDEM 1:   JGT PID1 PID2
            reg[regs[0]].locked = 1;
            regs[1] = get_filled_reg(temp.indexes[2][0], temp.indexes[2][1]); // REJESTR z tym PIDEM 2:   JGT PID1 PID2
            add_rmc_ins(RMC_SUB, regs[0], regs[1], -1); // odejmowanie PID1 - PID2
            add_rmc_ins(RMC_JZERO, regs[0], -1, lab[0]); // skacze do labela exit jesli bylo zle
            add_rmc_ins(RMC_JUMP, -1, -1, temp.indexes[0][0]); // udalo sie to skacze
            add_rmc_ins(RMC_LABEL, -1, -1, lab[0]); // tu skacze jesli nie jest GT
            
            reg[regs[0]].free = true;
            reg[regs[0]].must_store = false;
            reg[regs[0]].locked = 0;
            reg[regs[0]].index[0] = -1;
            reg[regs[0]].index[1] = -1;
            reg[regs[1]].free = true;
            reg[regs[1]].must_store = false;
            reg[regs[1]].locked = 0;
            reg[regs[1]].index[0] = -1;
            reg[regs[1]].index[1] = -1;
            reset_regs();
            
        } else if(type == TAC_JLEQ) {
            reset_regs();
            regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // REJESTR z tym PIDEM 1:   JLEQ PID1 PID2
            reg[regs[0]].locked = 1;
            regs[1] = get_filled_reg(temp.indexes[2][0], temp.indexes[2][1]); // REJESTR z tym PIDEM 2:   JLEQ PID1 PID2
            
            add_rmc_ins(RMC_SUB, regs[0], regs[1], -1); // pierwsze odejmowanie
            add_rmc_ins(RMC_JZERO, regs[0], -1, temp.indexes[0][0]); // udalo sie jesli wyjedzie 0
            
            reg[regs[0]].free = true;
            reg[regs[0]].must_store = false;
            reg[regs[0]].locked = 0;
            reg[regs[0]].index[0] = -1;
            reg[regs[0]].index[1] = -1;
            reg[regs[1]].free = false;
            reg[regs[1]].must_store = false;
            reg[regs[1]].locked = 0;
            reg[regs[1]].index[0] = temp.indexes[2][0];
            reg[regs[1]].index[1] = temp.indexes[2][1];
            reset_regs();
            
        } else if(type == TAC_JGEQ) {
            reset_regs();
            regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // REJESTR z tym PIDEM 1:   JGEQ PID1 PID2
            reg[regs[0]].locked = 1;
            regs[1] = get_filled_reg(temp.indexes[2][0], temp.indexes[2][1]); // REJESTR z tym PIDEM 2:   JGEQ PID1 PID2
            
            add_rmc_ins(RMC_SUB, regs[1], regs[0], -1); // pierwsze odejmowanie
            add_rmc_ins(RMC_JZERO, regs[1], -1, temp.indexes[0][0]); // udalo sie jesli wyjedzie 0
            
            reg[regs[0]].free = false;
            reg[regs[0]].must_store = false;
            reg[regs[0]].locked = 0;
            reg[regs[0]].has_val = false;
            reg[regs[0]].value = -1;
            reg[regs[0]].index[0] = temp.indexes[1][0];
            reg[regs[0]].index[1] = temp.indexes[1][1];
            reg[regs[1]].free = true;
            reg[regs[1]].must_store = false;
            reg[regs[1]].locked = 0;
            reg[regs[1]].has_val = false;
            reg[regs[1]].value = -1;
            reg[regs[1]].index[0] = -1;
            reg[regs[1]].index[1] = -1;
            reset_regs();
            
        } else if(type == TAC_ADD) {
            if(temp.indexes[0][1] == -1) { // jezeli to zmienna to szuka czy przypadkiem nie ma w jakims rejestrze typu ARR[VAR]
                reg_arr_var_store(temp.indexes[0][0]);
            }

            reset_regs();
            regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // REJESTR z tym co jest w ONE po prawej str:   PID := ONE + TWO
            reg[regs[0]].locked = 1;
            regs[1] = get_filled_reg(temp.indexes[2][0], temp.indexes[2][1]); // REJESTR z tym co jest w TWO po prawej str:   PID := ONE + TWO
            
            add_rmc_ins(RMC_ADD, regs[0], regs[1], -1); // umieszcza wartosc ONE + TWO w pamieci tego PID'a

            reg[regs[0]].free = false;
            reg[regs[0]].must_store = true;
            reg[regs[0]].locked = 0;
            reg[regs[0]].has_val = false;
            reg[regs[0]].value = -1;
            reg[regs[0]].index[0] = temp.indexes[0][0];
            reg[regs[0]].index[1] = temp.indexes[0][1];
            reg[regs[1]].locked = 0;
            reg[regs[1]].free = false;
            reg[regs[1]].locked = 0;
            reg[regs[1]].must_store = false;
            reg[regs[1]].has_val = false;
            reg[regs[1]].value = -1;
            reset_regs();
            
        } else if(type == TAC_SUB) {
            if(temp.indexes[0][1] == -1) { // jezeli to zmienna to szuka czy przypadkiem nie ma w jakims rejestrze typu ARR[VAR]
                reg_arr_var_store(temp.indexes[0][0]);
            }

            reset_regs();
            regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // REJESTR z tym co jest w ONE po prawej str:   PID := ONE - TWO
            reg[regs[0]].locked = 1;
            regs[1] = get_filled_reg(temp.indexes[2][0], temp.indexes[2][1]); // REJESTR z tym co jest w TWO po prawej str:   PID := ONE - TWO
            
            add_rmc_ins(RMC_SUB, regs[0], regs[1], -1); // umieszcza wartosc ONE - TWO w pamieci tego PID'a

            reg[regs[0]].free = false;
            reg[regs[0]].must_store = true;
            reg[regs[0]].locked = 0;
            reg[regs[0]].has_val = false;
            reg[regs[0]].value = -1;
            reg[regs[0]].index[0] = temp.indexes[0][0];
            reg[regs[0]].index[1] = temp.indexes[0][1];
            reg[regs[1]].free = false;
            reg[regs[1]].locked = 0;
            reg[regs[1]].must_store = false;
            reg[regs[1]].has_val = false;
            reg[regs[1]].value = -1;
            store_reg(regs[0]);
            
        } else if(type == TAC_MUL) {
            bool arg_1_num = check_num(temp.indexes[1][0]);
            bool arg_2_num = check_num(temp.indexes[2][0]);

            if(temp.indexes[0][1] == -1) { // jezeli to zmienna to szuka czy przypadkiem nie ma w jakims rejestrze typu ARR[VAR]
                reg_arr_var_store(temp.indexes[0][0]);
            }
            
            reset_regs();

            if(arg_1_num && arg_2_num) { // (NUM * NUM) > MAX_ULL
                unsigned long long multiplier = get_sym_value(temp.indexes[1][0]);
                int multiplicand_index = temp.indexes[2][0];
                
                if(get_sym_value(temp.indexes[2][0]) > multiplier) {
                    multiplier = get_sym_value(temp.indexes[2][0]);
                    multiplicand_index = temp.indexes[1][0];
                }

                regs[0] = get_filled_reg(multiplicand_index, -1); // REJESTR z mnożną
                reg[regs[0]].locked = 1;
                forget_reg(temp.indexes[0][0], temp.indexes[0][1]);
                regs[1] = find_good_reg(); // REJESTR z byle czym
                
                add_rmc_ins(RMC_RESET, regs[1], -1, -1); // ustawia rej na 0
                
                while(multiplier > 0) {
                    int r = multiplier & 1;
                    multiplier >>= 1;
                    
                    if(r == 1) {
                        add_rmc_ins(RMC_ADD, regs[1], regs[0], -1);
                    }

                    if(multiplier != 0) {
                        add_rmc_ins(RMC_SHL, regs[0], -1, -1);
                    }
                }
                
                forget_reg(multiplicand_index, -1);
                reg[regs[1]].free = false;
                reg[regs[1]].must_store = true;
                reg[regs[1]].locked = 0;
                reg[regs[1]].index[0] = temp.indexes[0][0];
                reg[regs[1]].index[1] = temp.indexes[0][1];
                reset_regs();

            } else if(arg_1_num || arg_2_num) { // VAR * NUM || NUM * VAR 
                int index_1;
                int index_2;
                unsigned long long multiplier;
                
                if(arg_1_num) {
                    multiplier = get_sym_value(temp.indexes[1][0]);
                    index_1 = temp.indexes[2][0];
                    index_2 = temp.indexes[2][1];
                } else {
                    multiplier = get_sym_value(temp.indexes[2][0]);
                    index_1 = temp.indexes[1][0];
                    index_2 = temp.indexes[1][1];
                }

                regs[0] = get_filled_reg(index_1, index_2); // REJESTR z mnożną
                reg[regs[0]].locked = 1;
                regs[1] = find_good_reg(); // REJESTR z byle czym
                add_rmc_ins(RMC_RESET, regs[1], -1, -1); // ustawia rej na 0
                
                while(multiplier > 0) {
                    int r = multiplier & 1;
                    multiplier >>= 1;
                    
                    if(r == 1) {
                        add_rmc_ins(RMC_ADD, regs[1], regs[0], -1);
                    }

                    if(multiplier != 0) {
                        add_rmc_ins(RMC_SHL, regs[0], -1, -1);
                    }
                }
                
                reg[regs[0]].free = true;
                reg[regs[0]].must_store = false;
                reg[regs[0]].locked = 0;
                reg[regs[0]].has_val = false;
                reg[regs[0]].value = -1;
                reg[regs[0]].index[0] = -1;
                reg[regs[0]].index[1] = -1;
                
                reg[regs[1]].free = false;
                reg[regs[1]].must_store = true;
                reg[regs[1]].locked = 0;
                reg[regs[1]].has_val = false;
                reg[regs[1]].value = -1;
                reg[regs[1]].index[0] = temp.indexes[0][0];
                reg[regs[1]].index[1] = temp.indexes[0][1];
                reset_regs();
                
                
            } else { // VAR * VAR
                reset_regs();
                regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // REJESTR z VAR1
                reg[regs[0]].locked = 1;
                regs[1] = get_filled_reg(temp.indexes[2][0], temp.indexes[2][1]); // REJESTR z VAR2
                reg[regs[1]].locked = 1;
                regs[2] = find_good_reg(); // REJESTR z byle czym
                regs[3] = find_good_reg(); // REJESTR z byle czym
                
                add_rmc_ins(RMC_RESET, regs[2], -1, -1); // ustawia rej na 0
                add_rmc_ins(RMC_RESET, regs[3], -1, -1); // ustawia rej na 0
            
                if(regs[0] != regs[1]) {
                    lab[0] = l_counter;
                    l_counter++;
                    add_rmc_ins(RMC_ADD, regs[2], regs[0], -1);
                    add_rmc_ins(RMC_SUB, regs[2], regs[1], -1);
                    add_rmc_ins(RMC_JZERO, regs[2], -1, lab[0]);
                    
                    add_rmc_ins(RMC_RESET, regs[2], -1, -1); // tutaj VAR_2 jest mniejsze to ustaw na multiplier
                    add_rmc_ins(RMC_ADD, regs[2], regs[0], -1); // multiplicand
                    add_rmc_ins(RMC_ADD, regs[3], regs[1], -1); // multiplier
                    lab[1] = l_counter;
                    l_counter++;
                    add_rmc_ins(RMC_JUMP, -1, -1, lab[1]);
                    add_rmc_ins(RMC_LABEL, -1, -1, lab[0]);
                }
                
                add_rmc_ins(RMC_ADD, regs[2], regs[1], -1); // multiplicand
                add_rmc_ins(RMC_ADD, regs[3], regs[0], -1); // multiplier
                reg[regs[0]].free = false;
                reg[regs[0]].must_store = false;
                reg[regs[0]].locked = 0;
                reg[regs[1]].free = false;
                reg[regs[1]].must_store = false;
                reg[regs[1]].locked = 0;
                
                
                if(regs[0] != regs[1]) {
                    add_rmc_ins(RMC_LABEL, -1, -1, lab[1]);
                }

                regs[4] = find_good_reg(); // REJESTR z byle czym
                add_rmc_ins(RMC_RESET, regs[4], -1, -1); // ustawia rej na 0
                
                lab[0] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_LABEL, -1, -1, lab[0]); // petla
                lab[1] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JZERO, regs[3], -1, lab[1]); // multiplier == 0 to koniec
                lab[2] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JODD, regs[3], -1, lab[2]); // jesli multiplier & 1 == 1 to jump
                add_rmc_ins(RMC_SHL, regs[2], -1, -1); // przesun multiplicand w lewo o 1
                add_rmc_ins(RMC_SHR, regs[3], -1, -1); // przesun multiplier w prawo o 1
                add_rmc_ins(RMC_JUMP, -1, -1, lab[0]);
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[2]); // bylo 1 czyli 
                add_rmc_ins(RMC_ADD, regs[4], regs[2], -1); // do wyniku dodaj multiplicand odpowiednio przesuniety
                add_rmc_ins(RMC_SHL, regs[2], -1, -1); // przesun multiplicand w lewo o 1
                add_rmc_ins(RMC_SHR, regs[3], -1, -1); // przesun multiplier w prawo o 1
                add_rmc_ins(RMC_JUMP, -1, -1, lab[0]);
                add_rmc_ins(RMC_LABEL, -1, -1, lab[1]); // koniec
                
                reg[regs[0]].free = true;
                reg[regs[0]].must_store = false;
                reg[regs[0]].locked = 0;
                reg[regs[0]].has_val = false;
                reg[regs[0]].value = -1;
                reg[regs[0]].index[0] = -1;
                reg[regs[0]].index[1] = -1;
                
                reg[regs[1]].free = true;
                reg[regs[1]].must_store = false;
                reg[regs[1]].locked = 0;
                reg[regs[1]].has_val = false;
                reg[regs[1]].value = -1;
                reg[regs[1]].index[0] = -1;
                reg[regs[1]].index[1] = -1;
                
                reg[regs[2]].free = true;
                reg[regs[2]].must_store = false;
                reg[regs[2]].locked = 0;
                reg[regs[2]].has_val = false;
                reg[regs[2]].value = -1;
                reg[regs[2]].index[0] = -1;
                reg[regs[2]].index[1] = -1;
                
                reg[regs[3]].free = true;
                reg[regs[3]].must_store = false;
                reg[regs[3]].locked = 0;
                reg[regs[3]].has_val = false;
                reg[regs[3]].value = -1;
                reg[regs[3]].index[0] = -1;
                reg[regs[3]].index[1] = -1;
                
                reg[regs[4]].free = false;
                reg[regs[4]].must_store = true;
                reg[regs[4]].locked = 0;
                reg[regs[4]].has_val = false;
                reg[regs[4]].value = -1;
                reg[regs[4]].index[0] = temp.indexes[0][0];
                reg[regs[4]].index[1] = temp.indexes[0][1];
                reset_regs();
            }
            
        } else if(type == TAC_DIV) {
            if(temp.indexes[0][1] == -1) { // jezeli to zmienna to szuka czy przypadkiem nie ma w jakims rejestrze typu ARR[VAR]
                reg_arr_var_store(temp.indexes[0][0]);
            }
            
            reset_regs();
            
            bool arg_2_num = check_num(temp.indexes[2][0]);
            
            if(arg_2_num && (get_sym_value(temp.indexes[2][0]) & (get_sym_value(temp.indexes[2][0]) - 1)) == 0) { // przypadek VAR / NUM gdzie NUM = 2^x
                int power = log(get_sym_value(temp.indexes[2][0])) / log(2.0);
                regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]);
                reg[regs[0]].locked = 1;
                regs[1] = find_good_reg(); // REJESTR z byle czym
                add_rmc_ins(RMC_RESET, regs[1], -1, -1);
                add_rmc_ins(RMC_ADD, regs[1], regs[0], -1);

                for(int i = 0; i < power; i++) {
                    add_rmc_ins(RMC_SHR, regs[1], -1, -1); // przesun w prawo o 1
                }
                
                reg[regs[0]].free = true;
                reg[regs[0]].must_store = false;
                reg[regs[0]].locked = 0;
                reg[regs[0]].has_val = false;
                reg[regs[0]].value = -1;
                reg[regs[0]].index[0] = -1;
                reg[regs[0]].index[1] = -1;
                reg[regs[1]].free = false;
                reg[regs[1]].must_store = true;
                reg[regs[1]].locked = 0;
                reg[regs[1]].has_val = false;
                reg[regs[1]].value = -1;
                reg[regs[1]].index[0] = temp.indexes[0][0];
                reg[regs[1]].index[1] = temp.indexes[0][1];
                reset_regs();
                
            } else { // przypadek pozostały
                reset_regs();
                regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // dividend
                reg[regs[0]].locked = 1;
                regs[1] = get_filled_reg(temp.indexes[2][0], temp.indexes[2][1]); // divisor
                reg[regs[1]].locked = 1;
                regs[2] = find_good_reg(); // REJESTR z przyszlym wynikiem
                regs[3] = find_good_reg(); // REJESTR z przyszlą resztą
                regs[4] = find_good_reg(); // REJESTR do obliczen
                regs[5] = find_good_reg(); // REJESTR do obliczen
                
                add_rmc_ins(RMC_RESET, regs[2], -1, -1);
                
                lab[0] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JZERO, regs[1], -1, lab[0]); // divisor == 0 to label 0
                
                lab[1] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_DEC, regs[1], -1, -1); // -1
                add_rmc_ins(RMC_JZERO, regs[1], -1, lab[1]); // divisor == 1 to label 1
                
                
                lab[2] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_DEC, regs[1], -1, -1); // -1
                add_rmc_ins(RMC_JZERO, regs[1], -1, lab[2]); // divisor == 2 to label 2
                add_rmc_ins(RMC_INC, regs[1], -1, -1); // +1
                add_rmc_ins(RMC_INC, regs[1], -1, -1); // +1 powrot do stanu sprzed sprawdzania
                
                add_rmc_ins(RMC_RESET, regs[3], -1, -1);
                add_rmc_ins(RMC_ADD, regs[3], regs[0], -1); // do reszty kopiujemy dividend'a
                
                add_rmc_ins(RMC_RESET, regs[2], -1, -1); // wynik to 0, bedzie budowany iteracyjnie

                add_rmc_ins(RMC_RESET, regs[5], -1, -1); // reset rej do obliczen
                add_rmc_ins(RMC_INC, regs[5], -1, -1); // do rej kopiujemy divisor'a
                
                lab[5] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_LABEL, -1, -1, lab[5]); // label 5
                add_rmc_ins(RMC_RESET, regs[4], -1, -1); // reset rej do obliczen
                add_rmc_ins(RMC_ADD, regs[4], regs[1], -1); // do rej kopiujemy divisor'a
                add_rmc_ins(RMC_SUB, regs[4], regs[3], -1); // odejmujemy dividend'a
                lab[6] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JZERO, regs[4], -1, lab[6]); // jump do 6 jesli 0
                lab[7] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JUMP, -1, -1, lab[7]); // jump do 7
                add_rmc_ins(RMC_LABEL, -1, -1, lab[6]); // label 6
                add_rmc_ins(RMC_SHL, regs[1], -1, -1); // przesun divisor'a w lewo o 1
                add_rmc_ins(RMC_SHL, regs[5], -1, -1); // przesun countera w lewo o 1
                add_rmc_ins(RMC_JUMP, -1, -1, lab[5]); // jump do 5
                
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[7]); // label 7
                
                add_rmc_ins(RMC_DEC, regs[5], -1, -1); // spr czy -1 da 0
                lab[4] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JZERO, regs[5], -1, lab[4]); // jump do 4 i koniec jesli 0
                add_rmc_ins(RMC_INC, regs[5], -1, -1); // powrot do prawidlowej wartosci
                add_rmc_ins(RMC_SHR, regs[1], -1, -1); // przesun divisor'a w lewo o 1
                add_rmc_ins(RMC_SHR, regs[5], -1, -1); // przesun divisor'a w lewo o 1
                
                add_rmc_ins(RMC_RESET, regs[4], -1, -1); // reset rej do obliczen
                add_rmc_ins(RMC_ADD, regs[4], regs[1], -1); // do rej kopiujemy divisor'a
                add_rmc_ins(RMC_SUB, regs[4], regs[3], -1); // odejmujemy dividend'a
                lab[8] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JZERO, regs[4], -1, lab[8]); // jump do 8 jesli 0
                add_rmc_ins(RMC_JUMP, -1, -1, lab[7]); // jump do 7
                add_rmc_ins(RMC_LABEL, -1, -1, lab[8]); // label 8
                add_rmc_ins(RMC_SUB, regs[3], regs[1], -1); // odejmujemy dividend'a
                add_rmc_ins(RMC_ADD, regs[2], regs[5], -1); // do wyniku dodajemy czesciowy wynik
                add_rmc_ins(RMC_JUMP, -1, -1, lab[7]); // jump do 7
                
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[0]); // koniec label 0
                add_rmc_ins(RMC_RESET, regs[3], -1, -1); // reszta to 0
                add_rmc_ins(RMC_JUMP, -1, -1, lab[4]); // skocz na koniec
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[1]); // koniec label 1
                add_rmc_ins(RMC_INC, regs[1], -1, -1); // +1
                add_rmc_ins(RMC_ADD, regs[2], regs[0], -1); // wynik to dividend
                add_rmc_ins(RMC_RESET, regs[3], -1, -1); // reszta to 0
                add_rmc_ins(RMC_JUMP, -1, -1, lab[4]); // skocz na koniec
                
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[2]); // koniec label 2
                add_rmc_ins(RMC_INC, regs[1], -1, -1); // +1
                add_rmc_ins(RMC_INC, regs[1], -1, -1); // +1
                add_rmc_ins(RMC_ADD, regs[2], regs[0], -1); // wynik to dividend / 2
                add_rmc_ins(RMC_SHR, regs[2], -1, -1); // przesun w prawo o 1
                lab[3] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_RESET, regs[3], -1, -1); // reszta to 0 jesli parzysta dividend
                add_rmc_ins(RMC_JODD, regs[0], -1, lab[3]); // dividend % 2 == 1 to reszta = 1
                
                add_rmc_ins(RMC_JUMP, -1, -1, lab[4]); // skocz na koniec
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[3]); // label 3 czyli nieparzysta
                add_rmc_ins(RMC_INC, regs[3], -1, -1); // +1 dla reszty
                
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[4]); // koniec dzielenia label 4


                reg[regs[0]].free = true;
                reg[regs[0]].must_store = false;
                reg[regs[0]].locked = 0;
                reg[regs[0]].index[0] = -1;
                reg[regs[0]].index[1] = -1;
                
                reg[regs[1]].free = true;
                reg[regs[1]].must_store = false;
                reg[regs[1]].locked = 0;
                reg[regs[1]].index[0] = -1;
                reg[regs[1]].index[1] = -1;
                
                reg[regs[2]].free = false;
                reg[regs[2]].must_store = true;
                reg[regs[2]].locked = 0;
                reg[regs[2]].has_val = false;
                reg[regs[2]].value = -1;
                reg[regs[2]].index[0] = temp.indexes[0][0];
                reg[regs[2]].index[1] = temp.indexes[0][1];
                
                reg[regs[3]].free = true;
                reg[regs[3]].must_store = false;
                reg[regs[3]].locked = 0;
                reg[regs[3]].index[0] = -1;
                reg[regs[3]].index[1] = -1;
                
                reg[regs[4]].free = true;
                reg[regs[4]].must_store = false;
                reg[regs[4]].locked = 0;
                reg[regs[4]].index[0] = -1;
                reg[regs[4]].index[1] = -1;
                
                reg[regs[5]].free = true;
                reg[regs[5]].must_store = false;
                reg[regs[5]].locked = 0;
                reg[regs[5]].index[0] = -1;
                reg[regs[5]].index[1] = -1;
                reset_regs();
            
            }
            
        } else if(type == TAC_MOD) {
            if(temp.indexes[0][1] == -1) { // jezeli to zmienna to szuka czy przypadkiem nie ma w jakims rejestrze typu ARR[VAR]
                reg_arr_var_store(temp.indexes[0][0]);
            }
            
            reset_regs();
            
            bool arg_2_num = check_num(temp.indexes[2][0]);
            
            if(arg_2_num && (get_sym_value(temp.indexes[2][0]) & (get_sym_value(temp.indexes[2][0]) - 1)) == 0) { // przypadek VAR % NUM gdzie NUM = 2^x
                int power = log(get_sym_value(temp.indexes[2][0])) / log(2.0);
                reset_regs();
                regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]);
                reg[regs[0]].locked = 1;
                regs[1] = find_good_reg(); // REJESTR z byle czym
                regs[2] = find_good_reg(); // REJESTR z byle czym
                regs[3] = find_good_reg(); // REJESTR z byle czym
                
                
                add_rmc_ins(RMC_RESET, regs[1], -1, -1);
                add_rmc_ins(RMC_ADD, regs[1], regs[0], -1);
                
                add_rmc_ins(RMC_RESET, regs[2], -1, -1);
                add_rmc_ins(RMC_INC, regs[2], -1, -1);
                add_rmc_ins(RMC_RESET, regs[3], -1, -1); // to bedzie wynik
                
                
                for(int i = 0; i < power; i++) {
                    lab[0] = l_counter;
                    l_counter++;
                    lab[1] = l_counter;
                    l_counter++;
                    add_rmc_ins(RMC_JODD, regs[1], -1, lab[0]); // divisor == 2 to label 2
                    add_rmc_ins(RMC_JUMP, -1, -1, lab[1]); // divisor == 2 to label 2
                    
                    add_rmc_ins(RMC_LABEL, -1, -1, lab[0]); // label 0
                    add_rmc_ins(RMC_ADD, regs[3], regs[2], -1); // do wyniku dodac to
                    
                    add_rmc_ins(RMC_LABEL, -1, -1, lab[1]); // label 1
                    add_rmc_ins(RMC_SHR, regs[1], -1, -1); // przesun w prawo o 1
                    add_rmc_ins(RMC_SHL, regs[2], -1, -1); // przesun w lewo o 1
                    
                }
                
                reg[regs[0]].free = true;
                reg[regs[0]].must_store = false;
                reg[regs[0]].locked = 0;
                reg[regs[0]].index[0] = -1;
                reg[regs[0]].index[1] = -1;
                
                
                reg[regs[1]].free = true;
                reg[regs[1]].must_store = false;
                reg[regs[1]].locked = 0;
                reg[regs[1]].index[0] = -1;
                reg[regs[1]].index[1] = -1;
                
                reg[regs[2]].free = true;
                reg[regs[2]].must_store = false;
                reg[regs[2]].locked = 0;
                reg[regs[2]].index[0] = -1;
                reg[regs[2]].index[1] = -1;
                
                reg[regs[3]].free = false;
                reg[regs[3]].must_store = true;
                reg[regs[3]].locked = 0;
                reg[regs[3]].index[0] = temp.indexes[0][0];
                reg[regs[3]].index[1] = temp.indexes[0][1];
                store_reg(regs[3]);
                
            } else { // przypadek pozostały
                reset_regs();
                regs[0] = get_filled_reg(temp.indexes[1][0], temp.indexes[1][1]); // dividend
                reg[regs[0]].locked = 1;
                regs[1] = get_filled_reg(temp.indexes[2][0], temp.indexes[2][1]); // divisor
                reg[regs[1]].locked = 1;
                regs[2] = find_good_reg(); // REJESTR z przyszlym wynikiem
                regs[3] = find_good_reg(); // REJESTR z przyszlą resztą
                regs[4] = find_good_reg(); // REJESTR do obliczen
                regs[5] = find_good_reg(); // REJESTR do obliczen
                
                add_rmc_ins(RMC_RESET, regs[2], -1, -1);
                
                lab[0] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JZERO, regs[1], -1, lab[0]); // divisor == 0 to label 0
                
                lab[1] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_DEC, regs[1], -1, -1); // -1
                add_rmc_ins(RMC_JZERO, regs[1], -1, lab[1]); // divisor == 1 to label 1
                
                
                lab[2] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_DEC, regs[1], -1, -1); // -1
                add_rmc_ins(RMC_JZERO, regs[1], -1, lab[2]); // divisor == 2 to label 2
                add_rmc_ins(RMC_INC, regs[1], -1, -1); // +1
                add_rmc_ins(RMC_INC, regs[1], -1, -1); // +1 powrot do stanu sprzed sprawdzania
                
                add_rmc_ins(RMC_RESET, regs[3], -1, -1);
                add_rmc_ins(RMC_ADD, regs[3], regs[0], -1); // do reszty kopiujemy dividend'a
                
                add_rmc_ins(RMC_RESET, regs[2], -1, -1); // wynik to 0, bedzie budowany iteracyjnie
                add_rmc_ins(RMC_RESET, regs[5], -1, -1); // reset rej do obliczen
                add_rmc_ins(RMC_INC, regs[5], -1, -1); // do rej kopiujemy divisor'a
                
                lab[5] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_LABEL, -1, -1, lab[5]); // label 5
                add_rmc_ins(RMC_RESET, regs[4], -1, -1); // reset rej do obliczen
                add_rmc_ins(RMC_ADD, regs[4], regs[1], -1); // do rej kopiujemy divisor'a
                add_rmc_ins(RMC_SUB, regs[4], regs[3], -1); // odejmujemy dividend'a
                lab[6] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JZERO, regs[4], -1, lab[6]); // jump do 6 jesli 0
                lab[7] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JUMP, -1, -1, lab[7]); // jump do 7
                add_rmc_ins(RMC_LABEL, -1, -1, lab[6]); // label 6
                add_rmc_ins(RMC_SHL, regs[1], -1, -1); // przesun divisor'a w lewo o 1
                add_rmc_ins(RMC_SHL, regs[5], -1, -1); // przesun countera w lewo o 1
                add_rmc_ins(RMC_JUMP, -1, -1, lab[5]); // jump do 5
                
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[7]); // label 7
                
                add_rmc_ins(RMC_DEC, regs[5], -1, -1); // spr czy -1 da 0
                lab[4] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JZERO, regs[5], -1, lab[4]); // jump do 4 i koniec jesli 0
                add_rmc_ins(RMC_INC, regs[5], -1, -1); // powrot do prawidlowej wartosci
                add_rmc_ins(RMC_SHR, regs[1], -1, -1); // przesun divisor'a w lewo o 1
                add_rmc_ins(RMC_SHR, regs[5], -1, -1); // przesun divisor'a w lewo o 1
                
                add_rmc_ins(RMC_RESET, regs[4], -1, -1); // reset rej do obliczen
                add_rmc_ins(RMC_ADD, regs[4], regs[1], -1); // do rej kopiujemy divisor'a
                add_rmc_ins(RMC_SUB, regs[4], regs[3], -1); // odejmujemy dividend'a
                lab[8] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_JZERO, regs[4], -1, lab[8]); // jump do 8 jesli 0
                add_rmc_ins(RMC_JUMP, -1, -1, lab[7]); // jump do 7
                add_rmc_ins(RMC_LABEL, -1, -1, lab[8]); // label 8
                add_rmc_ins(RMC_SUB, regs[3], regs[1], -1); // odejmujemy dividend'a
                add_rmc_ins(RMC_ADD, regs[2], regs[5], -1); // do wyniku dodajemy czesciowy wynik
                add_rmc_ins(RMC_JUMP, -1, -1, lab[7]); // jump do 7

                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[0]); // koniec label 0
                add_rmc_ins(RMC_RESET, regs[3], -1, -1); // reszta to 0
                add_rmc_ins(RMC_JUMP, -1, -1, lab[4]); // skocz na koniec
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[1]); // koniec label 1
                add_rmc_ins(RMC_INC, regs[1], -1, -1); // +1
                add_rmc_ins(RMC_ADD, regs[2], regs[0], -1); // wynik to dividend
                add_rmc_ins(RMC_RESET, regs[3], -1, -1); // reszta to 0
                add_rmc_ins(RMC_JUMP, -1, -1, lab[4]); // skocz na koniec
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[2]); // koniec label 2
                add_rmc_ins(RMC_INC, regs[1], -1, -1); // +1
                add_rmc_ins(RMC_INC, regs[1], -1, -1); // +1
                add_rmc_ins(RMC_ADD, regs[2], regs[0], -1); // wynik to dividend / 2
                add_rmc_ins(RMC_SHR, regs[2], -1, -1); // przesun w prawo o 1
                lab[3] = l_counter;
                l_counter++;
                add_rmc_ins(RMC_RESET, regs[3], -1, -1); // reszta to 0 jesli parzysta dividend
                add_rmc_ins(RMC_JODD, regs[0], -1, lab[3]); // dividend % 2 == 1 to reszta = 1
                
                add_rmc_ins(RMC_JUMP, -1, -1, lab[4]); // skocz na koniec
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[3]); // label 3 czyli nieparzysta
                add_rmc_ins(RMC_INC, regs[3], -1, -1); // +1 dla reszty
                
                
                add_rmc_ins(RMC_LABEL, -1, -1, lab[4]); // koniec dzielenia label 4


                reg[regs[0]].locked = 0;
                reg[regs[1]].free = true;
                reg[regs[1]].must_store = false;
                reg[regs[1]].locked = 0;
                reg[regs[1]].index[0] = -1;
                reg[regs[1]].index[1] = -1;
                
                reg[regs[2]].free = false;
                reg[regs[2]].must_store = false;
                reg[regs[2]].locked = 0;
                reg[regs[2]].has_val = false;
                reg[regs[2]].value = -1;
                reg[regs[2]].index[0] = -1;
                reg[regs[2]].index[1] = -1;
                
                reg[regs[3]].free = false;
                reg[regs[3]].must_store = true;
                reg[regs[3]].locked = 0;
                reg[regs[3]].has_val = false;
                reg[regs[3]].value = -1;
                reg[regs[3]].index[0] = temp.indexes[0][0];
                reg[regs[3]].index[1] = temp.indexes[0][1];
                
                reg[regs[4]].free = true;
                reg[regs[4]].must_store = false;
                reg[regs[4]].locked = 0;
                reg[regs[4]].index[0] = -1;
                reg[regs[4]].index[1] = -1;
                
                reg[regs[5]].free = true;
                reg[regs[5]].must_store = false;
                reg[regs[5]].locked = 0;
                reg[regs[5]].index[0] = -1;
                reg[regs[5]].index[1] = -1;
                reset_regs();
            }
        
        } else if(type == TAC_RESET) {
            if(temp.indexes[0][1] == -1) { // jezeli to zmienna to szuka czy przypadkiem nie ma w jakims rejestrze typu ARR[VAR]
                reg_arr_var_store(temp.indexes[0][0]);
            }
            
            reset_regs();
            regs[0] = find_good_reg(); // REJESTR z byle czym
            add_rmc_ins(RMC_RESET, regs[0], -1, -1); // ustawia rej na 0
            reg[regs[0]].free = false;
            reg[regs[0]].must_store = true;
            reg[regs[0]].locked = 0;
            reg[regs[0]].index[0] = temp.indexes[0][0]; // ustawia indexy PIDA
            reg[regs[0]].index[1] = temp.indexes[0][1]; // ustawia indexy PIDA
            reset_regs();
            
        } else if(type == TAC_INC) {
            if(temp.indexes[0][1] == -1) { // jezeli to zmienna to szuka czy przypadkiem nie ma w jakims rejestrze typu ARR[VAR]
                reg_arr_var_store(temp.indexes[0][0]);
            }
            
            reset_regs();
            regs[0] = get_filled_reg(temp.indexes[0][0], temp.indexes[0][1]); // REJESTR z tym co jest w PID po prawej str:   INC PID
            add_rmc_ins(RMC_INC, regs[0], -1, -1); // zwieksza wartosc o 1 tego PID'a
            reg[regs[0]].free = false;
            reg[regs[0]].must_store = true;
            reg[regs[0]].locked = 0;
            reg[regs[0]].index[0] = temp.indexes[0][0];
            reg[regs[0]].index[1] = temp.indexes[0][1];
            reset_regs();
            
        } else if(type == TAC_DEC) {
            if(temp.indexes[0][1] == -1) { // jezeli to zmienna to szuka czy przypadkiem nie ma w jakims rejestrze typu ARR[VAR]
                reg_arr_var_store(temp.indexes[0][0]);
            }
            
            reset_regs();
            regs[0] = get_filled_reg(temp.indexes[0][0], temp.indexes[0][1]); // REJESTR z tym co jest w PID po prawej str:   DEC PID
            add_rmc_ins(RMC_DEC, regs[0], -1, -1); // zmniejsza wartosc o 1 tego PID'a
            reg[regs[0]].free = false;
            reg[regs[0]].must_store = true;
            reg[regs[0]].locked = 0;
            reg[regs[0]].index[0] = temp.indexes[0][0];
            reg[regs[0]].index[1] = temp.indexes[0][1];
            reset_regs();
            
        } else if(type == TAC_SHR) {
            if(temp.indexes[0][1] == -1) { // jezeli to zmienna to szuka czy przypadkiem nie ma w jakims rejestrze typu ARR[VAR]
                reg_arr_var_store(temp.indexes[0][0]);
            }
            
            reset_regs();
            regs[0] = get_filled_reg(temp.indexes[0][0], temp.indexes[0][1]); // REJESTR z tym co jest w PID po prawej str:   SHR PID
            add_rmc_ins(RMC_SHR, regs[0], -1, -1); // przesuwa bitowo w prawo o 1 tego PID'a
            reg[regs[0]].free = false;
            reg[regs[0]].must_store = true;
            reg[regs[0]].locked = 0;
            reg[regs[0]].index[0] = temp.indexes[0][0];
            reg[regs[0]].index[1] = temp.indexes[0][1];
            reset_regs();
        
        } else if(type == TAC_SHL) {
            if(temp.indexes[0][1] == -1) { // jezeli to zmienna to szuka czy przypadkiem nie ma w jakims rejestrze typu ARR[VAR]
                reg_arr_var_store(temp.indexes[0][0]);
            }
            
            reset_regs();
            regs[0] = get_filled_reg(temp.indexes[0][0], temp.indexes[0][1]); // REJESTR z tym co jest w PID po prawej str:   SHL PID
            add_rmc_ins(RMC_SHL, regs[0], -1, -1); // przesuwa bitowo w lewo o 1 tego PID'a
            reg[regs[0]].free = false;
            reg[regs[0]].must_store = true;
            reg[regs[0]].locked = 0;
            reg[regs[0]].index[0] = temp.indexes[0][0];
            reg[regs[0]].index[1] = temp.indexes[0][1];
            reset_regs();
            
        } else if(type == TAC_READ) {
            reset_regs();
            regs[0] = get_address_filled_reg(temp.indexes[0][0], temp.indexes[0][1]); // REJESTR z adresem VAR || ARR[NUM] || ARR[VAR}
            forget_reg(temp.indexes[0][0], temp.indexes[0][1]);
            add_rmc_ins(RMC_GET, regs[0], -1, -1); // wczytuje do pamieci wskazywanej przez rej
            add_rmc_ins(RMC_LOAD, regs[0], regs[0], -1); // wczytuje do rej wartosc z tej pamieci
            
            reg[regs[0]].free = false;
            reg[regs[0]].must_store = false;
            reg[regs[0]].locked = 0;
            reg[regs[0]].has_val = false;
            reg[regs[0]].value = -1;
            reg[regs[0]].index[0] = temp.indexes[0][0];
            reg[regs[0]].index[1] = temp.indexes[0][1];
            reset_regs();
            
        } else if(type == TAC_WRITE) {
            reset_regs();

            if(check_num(temp.indexes[0][0])) { // musimy wypisac stala, sprawdzamy czy jest w pamieci
                if(!sym_table->symbols[temp.indexes[0][0]].num_in_mem) { // nie ma w pamieci to dadajemy
                    regs[0] = get_filled_reg(temp.indexes[0][0], temp.indexes[0][1]); // REJESTR z stala NUM
                    reg[regs[0]].locked = 1;
                    regs[1] = get_address_filled_reg(temp.indexes[0][0], temp.indexes[0][1]); // REJESTR z adresem tego NUM'a
                    
                    add_rmc_ins(RMC_STORE, regs[0], regs[1], -1); // umieszcza wartosc NUM'a w pamieci tego NUM'a
                    sym_table->symbols[temp.indexes[0][0]].num_in_mem = true;
                    add_rmc_ins(RMC_PUT, regs[1], -1, -1); // wyswietla zawartosc pamieci pod adresem rejestru NUMA
                    reg[regs[0]].free = false;
                    reg[regs[0]].must_store = false;
                    reg[regs[0]].locked = 0;
                    reg[regs[0]].index[0] = temp.indexes[0][0];
                    reg[regs[0]].index[1] = temp.indexes[0][1];
                    reg[regs[1]].free = true;
                    reg[regs[1]].must_store = false;
                    reg[regs[1]].locked = 0;
                    reg[regs[1]].has_val = false;
                    reg[regs[1]].value = -1;
                    reg[regs[1]].index[0] = -1;
                    reg[regs[1]].index[1] = -1;
                    reset_regs();
                    
                } else { // num jest w pamieci to wywolujemy
                    regs[0] = get_address_filled_reg(temp.indexes[0][0], temp.indexes[0][1]); // REJESTR z adresem tego NUM'a
                    add_rmc_ins(RMC_PUT, regs[0], -1, -1); // wyswietla zawartosc pamieci pod adresem rejestru NUMA
                    reg[regs[0]].free = true;
                    reg[regs[0]].must_store = false;
                    reg[regs[0]].locked = 0;
                    reg[regs[0]].has_val = false;
                    reg[regs[0]].value = -1;
                    reg[regs[0]].index[0] = -1;
                    reg[regs[0]].index[1] = -1;
                    reset_regs();
                }
            } else {
                // sprawdza czy VAR || ARR[NUM] || ARR[VAR] jest w jakims rejestrze i czy trzeba koniecznie ja zapisac do memory
                int check = check_reg_filled(temp.indexes[0][0], temp.indexes[0][1]);

                if(check >= 0) {
                    if(reg[check].must_store) { // trzeba zapisac to do memory
                        store_reg(check);
                    }
                }
                
                regs[0] = get_address_filled_reg(temp.indexes[0][0], temp.indexes[0][1]); // REJESTR z adresem tego VAR || ARR[NUM] || ARR[VAR]
                add_rmc_ins(RMC_PUT, regs[0], -1, -1); // wyswietla zawartosc pamieci pod adresem rejestru NUMA
                reg[regs[0]].free = true;
                reg[regs[0]].must_store = false;
                reg[regs[0]].locked = 0;
                reg[regs[0]].has_val = false;
                reg[regs[0]].value = -1;
                reg[regs[0]].index[0] = -1;
                reg[regs[0]].index[1] = -1;
                reset_regs();
            }
            
        }
    }
    add_rmc_ins(RMC_HALT, -1, -1, -1); // HALT KONIEC
}



int check_if_div_calculated(int i_10, int i_11, int i_20, int i_21) {
    int temp = -1;
    
    for(int i = 0; i < 6; i++) {
        if(reg[i].ins.type == TAC_DIV) {
            if(reg[i].ins.indexes[1][0] == i_10 && reg[i].ins.indexes[1][1] == i_11
                && reg[i].ins.indexes[2][0] == i_20 && reg[i].ins.indexes[2][1] == i_21) {
                temp = i;
            }
        }
    }
    
    return temp;
}

int check_if_mod_calculated(int i_10, int i_11, int i_20, int i_21) {
    int temp = -1;
    
    for(int i = 0; i < 6; i++) {
        if(reg[i].ins.type == TAC_MOD) {
            if(reg[i].ins.indexes[1][0] == i_10 && reg[i].ins.indexes[1][1] == i_11
                && reg[i].ins.indexes[2][0] == i_20 && reg[i].ins.indexes[2][1] == i_21) {
                temp = i;
            }
        }
    }
    
    return temp;
}


void count_rmcs() {
    int counter = 0;
    int size = program_rmc->size;
    
    for(int i = 0; i < size; i++) {
        if(program_rmc->rmc_s[i].type != RMC_LABEL) {
            program_rmc->rmc_s[i].counter = counter;
            counter++;
        } else {
            program_rmc->rmc_s[i].counter = counter;
        }
    }
}

void fix_jump_counter() {
    int size = program_rmc->size;
    
    for(int i = 0; i < size; i++) {
        rmc_type type = program_rmc->rmc_s[i].type;
        
        if(type == RMC_JUMP || type == RMC_JZERO || type == RMC_JODD) {
            for(int j = 0; j < size; j++) {
                rmc_type type_2 = program_rmc->rmc_s[j].type;

                if(type_2 == RMC_LABEL && program_rmc->rmc_s[i].jump_dest == program_rmc->rmc_s[j].jump_dest) {
                    int result = program_rmc->rmc_s[j].counter - program_rmc->rmc_s[i].counter;
                    program_rmc->rmc_s[i].jump_dest = result;
                    break;
                }
            }
        }
    }
}


void free_sym_table() {
    for(int i = 0; i < sym_table->size; i++) {
        free(sym_table->symbols[i].name);
    }
    free(sym_table->symbols);
    free(sym_table);
}

void free_ast_r(AstNode* node) {
    if(node == NULL) {
        return;
    }
    
    for(int i = 0; i < node->size; i++) {
        if(node->nodes != NULL && node->nodes[i] != NULL) {
            free_ast_r(node->nodes[i]);
        }
    }
    
    if(node->nodes != NULL) {
        free(node->nodes);
    }

    free(node);
}

void free_ast() {
    free_ast_r(program_ast);
}


void free_tac() {
    free(program_tac->tac_s);
    free(program_tac);
}

void free_tac_o() {
    free(program_tac_o->tac_s);
    free(program_tac_o);
}

void free_rmc() {
    free(program_rmc->rmc_s);
    free(program_rmc);
}

void free_all() {
    free_sym_table();
    free_ast();
    free_tac();
    free_tac_o();
    free_rmc();
}


const char rmc_instructions[][8] = {
    "GET",
    "PUT",
    "LOAD",
    "STORE",
    "ADD",
    "SUB",
    "RESET",
    "INC",
    "DEC",
    "SHR",
    "SHL",
    "JUMP",
    "JZERO",
    "JODD",
    "LABEL",
    "HALT"
};

const char reg_symbols[][2] = {
    "a",
    "b",
    "c",
    "d",
    "e",
    "f"
};

void print_clean_rmc(void) {
    cout << endl;

    for(int i = 0; i < program_rmc->size; i++){
        if(program_rmc->rmc_s[i].type == RMC_LABEL) {
            continue;
        }

        cout << rmc_instructions[program_rmc->rmc_s[i].type];
            
        if(program_rmc->rmc_s[i].index[0] >= 0) {
            cout << " " << reg_symbols[program_rmc->rmc_s[i].index[0]];
        }

        if(program_rmc->rmc_s[i].index[1] >= 0) {
            cout << " " << reg_symbols[program_rmc->rmc_s[i].index[1]];
        }
                
        if(program_rmc->rmc_s[i].jump_dest != -1) {
            cout << " " << program_rmc->rmc_s[i].jump_dest;
        }

        cout << endl;
    }
    cout << endl;
}

void print_clean_rmc_file(void) {
    for(int i = 0; i < program_rmc->size; i++){
        if(program_rmc->rmc_s[i].type == RMC_LABEL) {
            continue;
        }

        output_file << rmc_instructions[program_rmc->rmc_s[i].type];
            
        if(program_rmc->rmc_s[i].index[0] >= 0) {
            output_file << " " << reg_symbols[program_rmc->rmc_s[i].index[0]];
        }

        if(program_rmc->rmc_s[i].index[1] >= 0) {
            output_file << " " << reg_symbols[program_rmc->rmc_s[i].index[1]];
        }
                
        if(program_rmc->rmc_s[i].jump_dest != -1) {
            output_file << " " << program_rmc->rmc_s[i].jump_dest;
        }

        output_file << endl;        
    }
    output_file << endl;
}

int yyparse();
extern FILE* yyin;

int main(int argc, char** argv) {
    if(argc > 2) {
        yyin = fopen(argv[1], "r");
        output_file.open(argv[2]);
    } else {
        cout << "Argument error! Try again!" << endl;
        return 1;
    }
    
    sym_table_init();
    yyparse();
    set_mems();
    fclose(yyin);
    init_TAC_program();
    trans_ast_to_tac();
    tac_optimize();
    count_blocks();
    init_registers();
    init_RMC_program();
    tac_to_rmc();
    count_rmcs();
    fix_jump_counter();
    print_clean_rmc_file();
    output_file.close();
    free_all();
    
    return 0;
}
