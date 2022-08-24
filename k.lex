%option noyywrap
%option nounput
%option noinput
%option yylineno
%{
#include "k_lib.h"
#include "k_y.h"
#include <string.h>
#include <iostream>
using namespace std;

int scope = 0;
%}

%s for_pid

%%

[ \t\r]+
\[[^\]]*\]

"DECLARE"     {return DECLARE;}
"BEGIN"       {return _BEGIN_;}
"END"         {return END;}
"IF"          {scope++; return IF;}
"THEN"        {return THEN;}
"ELSE"        {return ELSE;}
"ENDIF"       {scope--; return ENDIF;}
"WHILE"       {scope++; return WHILE;}
"DO"          {return DO;}
"ENDWHILE"    {scope--; return ENDWHILE;}
"REPEAT"      {scope++; return REPEAT;}
"UNTIL"       {scope--; return UNTIL;}
"FOR"         {scope++; BEGIN(for_pid); return FOR;}
"FROM"        {return FROM;}
"TO"          {return TO;}
"DOWNTO"      {return DOWNTO;}
"ENDFOR"      {manage_scope(scope); scope--; return ENDFOR;}
"READ"        {return READ;}
"WRITE"       {return WRITE;}

"+"         {return ADD;}
"-"         {return SUB;}
"*"         {return MUL;}
"/"         {return DIV;}
"%"         {return MOD;}

"="         {return EQ;}
"!="        {return NEQ;}
"<"         {return LT;}
">"         {return GT;}
"<="        {return LEQ;}
">="        {return GEQ;}

"("         {return LBR;}
")"         {return RBR;}

":="        {yylval.lineno = yylineno; return ASSIGN;}
":"         {return COLON;}
";"         {return SEMICOLON;}
","         {return COMMA;}


\n

<for_pid>[_a-z]+    {yylval.iden_lineno.lineno = yylineno; yylval.iden_lineno.scope = scope; yylval.iden_lineno.id = strdup(yytext); int temp = add_iter_symbol(yylval.iden_lineno.id, scope); if(temp < 0) {error_2();} yylval.iden_lineno.iden = temp; BEGIN(INITIAL); return FOR_PIDENTIFIER;}
[0-9]+              {yylval.id_lineno.id = strdup(yytext); return NUM;}
[_a-z]+             {yylval.id_lineno.lineno = yylineno; yylval.id_lineno.id = strdup(yytext); return PIDENTIFIER;}

.           {return ERR;}


%%
