%define parse.error verbose
%{
#include <math.h>
#include <stdio.h>
#include <iostream>
#include <string>
#include <cstring>
#include "k_lib.h"
using namespace std;

int yylex(void);
void yyerror(string s);
extern int LC;
extern int yylineno;
%}
%union{
    AstNode* node;
    char* id;
    int lineno;
    struct id_lineno {
        char* id;
        int lineno;
    } id_lineno;
    struct iden_lineno {
        int iden;
        char* id;
        int lineno;
        int scope;
    } iden_lineno;
}

%token DECLARE _BEGIN_ END
%token IF THEN ELSE ENDIF
%token WHILE DO ENDWHILE
%token REPEAT UNTIL
%token FOR FROM TO DOWNTO ENDFOR
%token READ WRITE

%token ADD SUB MUL DIV MOD
%token EQ NEQ LT GT LEQ GEQ
%token LBR RBR
%token ASSIGN COLON SEMICOLON COMMA
%token NUM PIDENTIFIER FOR_PIDENTIFIER
%type <lineno> ASSIGN
%type <id_lineno> NUM
%type <id_lineno> PIDENTIFIER
%type <iden_lineno> FOR_PIDENTIFIER
%type <node> commands
%type <node> command
%type <node> expression
%type <node> condition
%type <node> identifier
%type <node> identifier_expr
%type <node> value
%token ERR

%%
program:
    DECLARE declarations _BEGIN_ commands END                 {build_program_ast($4);}
    | _BEGIN_ commands END                                    {build_program_ast($2);}
    ;

declarations:
    declarations COMMA var_declaration
    | declarations COMMA arr_declaration 
    | var_declaration
    | arr_declaration
    ;

var_declaration:
    PIDENTIFIER                                             {int temp = add_symbol($1.id); if(temp < 0) {error_1($1.id, $1.lineno);} else {if(!set_symbol_type(temp)) {error_type_settings();}};}
    ;
    
arr_declaration:
    PIDENTIFIER LBR NUM COLON NUM RBR                       {int temp = add_symbol($1.id); if(temp < 0) {error_1($1.id, $1.lineno);} else {if(!set_symbol_type(temp, $3.id, $5.id)) {error_arr_range($1.id);};}}
    ;

commands:
    commands command                                                {$$ = add_command($1, $2);}
    | command                                                       {AstNode* temp = init_commands_node(); $$ = add_command(temp, $1);}
    ;

command:
    identifier ASSIGN expression SEMICOLON                              {if(check_iter_modified($1)) {error_8($2);} $$ = init_par_node(AST_ASSIGN, $1, $3);}
    | IF condition THEN commands ELSE commands ENDIF                    {$$ = init_par_node(AST_IF_ELSE, $2, $4, $6);}
    | IF condition THEN commands ENDIF                                  {$$ = init_par_node(AST_IF, $2, $4);}
    | WHILE condition DO commands ENDWHILE                              {$$ = init_par_node(AST_WHILE, $2, $4);}
    | REPEAT commands UNTIL condition SEMICOLON                         {$$ = init_par_node(AST_REPEAT, $2, $4);}
    | FOR FOR_PIDENTIFIER FROM value TO value DO commands ENDFOR            {int temp = $2.iden; if(temp < 0) {error_2();} if(check_iter_loop(temp, $4, $6)) {error_7($2.id, $2.lineno);} $$ = init_par_node(AST_FOR_TO, init_num_node(AST_VAR, temp), init_num_node(AST_VAR, (temp + 1)), $4, $6, $8);}
    | FOR FOR_PIDENTIFIER FROM value DOWNTO value DO commands ENDFOR        {int temp = $2.iden; if(check_iter_loop(temp, $4, $6)) {error_7($2.id, $2.lineno);} $$ = init_par_node(AST_FOR_DOWNTO, init_num_node(AST_VAR, temp), init_num_node(AST_VAR, (temp + 1)), $4, $6, $8);}
    | READ identifier SEMICOLON                                         {$$ = init_par_node(AST_READ, $2);}
    | WRITE value SEMICOLON                                             {$$ = init_par_node(AST_WRITE, $2);}
    ;



expression:
    value                                                       {$$ = $1;}
    | value ADD value                                           {$$ = init_par_node(AST_ADD, $1, $3);}
    | value SUB value                                           {$$ = init_par_node(AST_SUB, $1, $3);}
    | value MUL value                                           {$$ = init_par_node(AST_MUL, $1, $3);}
    | value DIV value                                           {$$ = init_par_node(AST_DIV, $1, $3);}
    | value MOD value                                           {$$ = init_par_node(AST_MOD, $1, $3);}
    ;

condition:
    value EQ value                                              {$$ = init_par_node(AST_EQ, $1, $3);}
    | value NEQ value                                           {$$ = init_par_node(AST_NEQ, $1, $3);}
    | value LT value                                            {$$ = init_par_node(AST_LT, $1, $3);}
    | value GT value                                            {$$ = init_par_node(AST_GT, $1, $3);}
    | value LEQ value                                           {$$ = init_par_node(AST_LEQ, $1, $3);}
    | value GEQ value                                           {$$ = init_par_node(AST_GEQ, $1, $3);}
    | value                                                     {$$ = $1;}
    ;

value:
    NUM                                                         {int temp = add_num_symbol($1.id); {$$ = init_num_node(AST_NUM, temp);}}
    | identifier_expr                                           {$$ = $1;}
    ;
    
identifier:
    PIDENTIFIER                                                 {int temp = check_var_decl($1.id); if(temp == -1) {error_3($1.id, $1.lineno);} else if(temp == -2) {error_4($1.id, $1.lineno);} else {{$$ = init_num_node(AST_VAR, temp, true);}}}
    | PIDENTIFIER LBR PIDENTIFIER RBR                           {int temp_1 = check_arr_decl($1.id); if(temp_1 == -1) {error_3($1.id, $1.lineno);} else if(temp_1 == -2) {error_5($1.id, $1.lineno);} int temp_2 = check_var_decl($3.id);
                                                                    if(temp_2 == -1) {error_3($3.id, $3.lineno);} else if(temp_2 == -2) {error_4($3.id, $3.lineno);} else {$$ = init_par_node(AST_ARR, init_num_node(AST_VAR, temp_1), init_num_node(AST_VAR, temp_2));}}
    | PIDENTIFIER LBR NUM RBR                                   {int temp_1 = check_arr_decl($1.id); if(temp_1 == -1) {error_3($1.id, $1.lineno);} else if(temp_1 == -2) {error_5($1.id, $1.lineno);} int temp_2 = add_num_symbol($3.id); $$ = init_par_node(AST_ARR, init_num_node(AST_VAR, temp_1), init_num_node(AST_NUM, temp_2));}
    ;

identifier_expr:
    PIDENTIFIER                                                 {int temp = check_var_decl($1.id); if(temp == -1) {error_3($1.id, $1.lineno);} else if(temp == -2) {error_4($1.id, $1.lineno);} else {
                                                                    if(!check_var_init(temp)) {error_6($1.id, $1.lineno);} else {$$ = init_num_node(AST_VAR, temp);}}}
    | PIDENTIFIER LBR PIDENTIFIER RBR                           {int temp_1 = check_arr_decl($1.id); if(temp_1 == -1) {error_3($1.id, $1.lineno);} else if(temp_1 == -2) {error_5($1.id, $1.lineno);} int temp_2 = check_var_decl($3.id);
                                                                    if(temp_2 == -1) {error_3($3.id, $3.lineno);} else if(temp_2 == -2) {error_4($3.id, $3.lineno);} else {
                                                                    if(!check_var_init(temp_2)) {error_6($3.id, $3.lineno);} else {$$ = init_par_node(AST_ARR, init_num_node(AST_VAR, temp_1), init_num_node(AST_VAR, temp_2));}}}
    | PIDENTIFIER LBR NUM RBR                                   {int temp_1 = check_arr_decl($1.id); if(temp_1 == -1) {error_3($1.id, $1.lineno);} else if(temp_1 == -2) {error_5($1.id, $1.lineno);} int temp_2 = add_num_symbol($3.id); $$ = init_par_node(AST_ARR, init_num_node(AST_VAR, temp_1), init_num_node(AST_NUM, temp_2));}
    ;

%%



void yyerror(string s) {
    cout << "ERROR - nierozpoznany napis. " << s << " w linii " << yylineno << endl;
    exit(1);
}

