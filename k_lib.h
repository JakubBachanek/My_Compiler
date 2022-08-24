
//--------------------------- SYMBOL TABLE -------------------

#define MAX_SIZE 256
#define NODE_MAX_SIZE 32
#define TAC_MAX_SIZE 1024
#define RMC_MAX_SIZE 4096


typedef enum s_type {
    NUMB,
    VAR,
    ARR,
    ITER,
    NONE
} s_type;

typedef struct Symbol {
    char* name;
    s_type type;
    bool is_initialized;
    bool num_in_mem;
    int scope;
    unsigned long long value;
    unsigned long long size;
    unsigned long long offset;
    unsigned long long mem_i;
} Symbol;

typedef struct SymbolTable {
    int max_size;
    int size;
    Symbol* symbols;
} SymbolTable;


void error_1(char* name, int lineno);
void error_2(void);
void error_3(char* name, int lineno);
void error_4(char* name, int lineno);
void error_5(char* name, int lineno);
void error_6(char* name, int lineno);
void error_7(char* name, int lineno);
void error_8(int lineno);
void error_type_settings(void);
void error_arr_range(char* name);
void manage_scope(int scope);
void sym_table_init(void);
void check_extend(void);
int check_declared(char* name);
int check_var_decl(char* name);
bool check_var_init(int index);
int check_arr_decl(char* name);
int check_num_symbol(char* name);
int add_iter_symbol(char* name, int scope);
int add_iter_num_symbol(char* name);
int check_iter_declared(char* name);
int add_symbol(char* name);
int add_num_symbol(char* name);
bool set_symbol_type(int index);
bool set_symbol_type(int index, char* start, char* end);





// ----------------------------- AST


typedef enum ast_node_type {
    AST_PROGRAM,
    AST_COMMANDS,
    AST_ASSIGN,
    AST_IF_ELSE,
    AST_IF,
    AST_WHILE,
    AST_REPEAT,
    AST_FOR_TO,
    AST_FOR_DOWNTO,
    AST_READ,
    AST_WRITE,
    AST_ADD,
    AST_SUB,
    AST_MUL,
    AST_DIV,
    AST_MOD,
    AST_EQ,
    AST_NEQ,
    AST_LT,
    AST_GT,
    AST_LEQ,
    AST_GEQ,
    AST_NUM,
    AST_VAR,
    AST_ARR
} ast_node_type;




typedef struct AstNode {
    int max_size;
    ast_node_type type;
    int size;
    int sym_index;
    AstNode** nodes;
} AstNode;


AstNode* init_commands_node(void);
void check_extend_ast(AstNode* node);
AstNode* add_command(AstNode* node_p, AstNode* node_c);
AstNode* init_par_node(ast_node_type type, AstNode* node_1);
AstNode* init_par_node(ast_node_type type, AstNode* node_1, AstNode* node_2);
AstNode* init_par_node(ast_node_type type, AstNode* node_1, AstNode* node_2, AstNode* node_3);
AstNode* init_par_node(ast_node_type type, AstNode* node_1, AstNode* node_2, AstNode* node_3, AstNode* node_4, AstNode* node_5);
AstNode* init_num_node(ast_node_type type, int index);
AstNode* init_num_node(ast_node_type type, int index, bool initialized);
bool check_iter_loop(int index, AstNode* node_1, AstNode* node_2);
bool check_iter_modified(AstNode* node);
void build_program_ast(AstNode* node);
void set_mems(void);
unsigned long long get_mem_arr_address(int arr_index, unsigned long long index_value);
unsigned long long get_mem_address(int index);

// -------------------------------- TAC

typedef enum tac_type {
    TAC_UNDEFINED,
    TAC_LABEL,
    TAC_ASSIGN,
    TAC_JUMP,
    TAC_JZERO,
    TAC_JEQ,
    TAC_JNEQ,
    TAC_JLT,
    TAC_JGT,
    TAC_JLEQ,
    TAC_JGEQ,
    TAC_ADD,
    TAC_SUB,
    TAC_MUL,
    TAC_DIV,
    TAC_MOD,
    TAC_RESET,
    TAC_INC,
    TAC_DEC,
    TAC_SHR,
    TAC_SHL,
    TAC_READ,
    TAC_WRITE
} tac_type;

typedef struct TAC_I {
    tac_type type;
    int size;
    int indexes[3][2];
    int b_index;
} TAC_I;

typedef struct TAC_program {
    int max_size;
    int size;
    TAC_I* tac_s;
} TAC_program;

void init_TAC_program(void);
void trans_ast_to_tac(void);
void check_extend_tac(void);
void add_tac_ins(tac_type type);
void add_ins_index(int index_1, int index_2);
void change_tac_ins(tac_type type);
void add_label(int index);
void ast_to_tac(AstNode* node);
void ast_replace_iterator(AstNode* node);
bool check_num(int index);
unsigned long long get_sym_value(int index);
void check_extend_tac_o(void);
void add_tac_o_ins(tac_type type);
void add_ins_o_index(int index_1, int index_2);
void tac_optimize(void);
void count_blocks();




// ------------------------- REGISTERS


typedef struct Register {
    bool free;
    int locked;
    bool must_store;
    int index[2];
    bool has_val;
    unsigned long long value;
    TAC_I ins;
} Register;


void init_registers();
void set_register(int r_index, unsigned long long value);
void gen_const(int index, unsigned long long value);
void reset_regs();
int check_reg_filled(int index_1, int index_2);
int check_filled_reg_value(unsigned long long value);
bool store_reg(int index);
int find_good_reg(void);
int find_f_s_reg(void);
int get_filled_reg(int index_1, int index_2);
int get_address_filled_reg(int i_1, int i_2);
void forget_reg(int index_1, int index_2);
void reg_arr_var_store(int index);


// ------------------------ REG MACHINE CODE

typedef enum rmc_type {
    RMC_GET, // 0
    RMC_PUT, // 1
    RMC_LOAD, // 2
    RMC_STORE, // 3
    RMC_ADD, // 4
    RMC_SUB, // 5
    RMC_RESET, // 6
    RMC_INC, // 7
    RMC_DEC, // 8
    RMC_SHR, // 9
    RMC_SHL, // 10
    RMC_JUMP, // 11
    RMC_JZERO, // 12
    RMC_JODD, // 13 
    RMC_LABEL,// 14
    RMC_HALT // 15
} rmc_type;

typedef struct RMC_I {
    rmc_type type;
    int counter;
    int index[2];
    int jump_dest;
} RMC_I;

typedef struct RMC_program {
    int max_size;
    int size;
    RMC_I* rmc_s;
} RMC_program;

void init_RMC_program(void);
void check_extend_rmc(void);
void add_rmc_ins(rmc_type type, int i_1, int i_2, int j_dest);
void tac_to_rmc(void);
int check_if_div_calculated(int i_10, int i_11, int i_20, int i_21);
int check_if_mod_calculated(int i_10, int i_11, int i_20, int i_21);
void count_rmcs();
void fix_jump_counter();

void free_sym_table();
void free_ast_r(AstNode* node);
void free_ast();
void free_tac();
void free_tac_o();
void free_rmc();
void free_all();
void print_rmc(void);
void print_clean_rmc(void);
void print_clean_rmc_file(void);


