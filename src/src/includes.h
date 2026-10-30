#ifndef __INCLUDES__H__
#define __INCLUDES__H__

/*
	-----------------------------------------------------------------------------------------------------------------------------------------------
																	calcul numérique
	-----------------------------------------------------------------------------------------------------------------------------------------------
*/

#include "dlist.h"

#define max(a,b) (a > b) ? a : b
#define LEN_NUMBER 512

typedef struct Number
{
	int signe;
	char* nombre;
}Number;

void factorialString(int n, char* result);
Number create(int signe, const char* nbr);
void free_Number(Number nbr);
Number sub(Number left, Number right);
Number add(Number left, Number right);
Number prod(Number left, Number right);
Number gcd(Number num, Number denom);
Number int_divid(Number num, Number denom, Number* rem);
Number divid(Number num, Number denom);
Number Logarithme(Number x);
Number Exponentiel(Number x);
Number ExponentiationRapide(Number base, Number exposant);

/*
	-----------------------------------------------------------------------------------------------------------------------------------------------
																RPN : Reverse Polish Notation 
	-----------------------------------------------------------------------------------------------------------------------------------------------
*/

#ifdef _EZ80

#undef NDEBUG
#include <debug.h>

#endif // _EZ80

typedef enum token
{
	NUMBER, VARIABLE, UNDEF, IMAGE, PI, INVERSE, CARRE, CUBE,
	/* OPÉRATOR */
	PAR_OUVRANT, PAR_FERMANT, ADD, SUB, PROD, DIVID, POW, FRACTION, SEPARATEUR,
	/* COMPARISON */
	EGAL, DIFFERENT, INFERIEUR, INFERIEUR_EGAL, SUPERIEUR, SUPERIEUR_EGAL,
	/* LOGIC */
	LOGIC_AND, LOGIC_OR,
	/* NEGATION */
	NEGATIF,
	/* FONCTION */
	EXP_F, SQRT_F, CBRT_F, LN_F, LOG_F, LOGBASE_F, TOK_10_POWER, ABS_F, SIGN_F, COS_F, SIN_F, TAN_F, ACOS_F, ASIN_F,
	ATAN_F, COSH_F, SINH_F, TANH_F, ACOSH_F, ASINH_F, ATANH_F, FACTORIEL_F, ROOT_F,
	/* COMPLEX FONCTION */
	CONJ_F, REEL_F, IMAGE_F, ANGLE_F,
	/* FONCTION CALCULS */
	DERIV_F, INTEGRAL_F, DESOLVE_F, TANG_F, REMAINDER_F, INT_F, GCD_F, POLYSIMP_F, EXPAND_F, FACTOR_F, TAYLOR_F,
	/* taille enum / invalid */
	AMOUNT_TOKEN, TOKEN_INVALID
}token;

typedef enum optype
{
	DECIMAL,
	ENT,
	VAR,
	NEGATION,
	FUNCTION,
	OPERAT,
	LOGIC
}optype;

typedef struct Tree
{
	char* value;
	struct Tree* tleft;
	struct Tree* tright;
	struct Tree* parent;
	optype gtype;
	token tok_type;
}Tree;

typedef struct table_token
{
	char ex[10];
	int length;
}table_token;

#define IS_NUMERIC(b) (((b) >= 0x30 && (b) <= 0x3A) || (b) == '.')
#define IS_VAR(b) (((b) >= 0x41 && (b) < 0x5B) || ((b) >= 'a' && (b) <= 'z') || (b) == 0xAE || (b) == '@' || (b) == '\'')

extern struct table_token ti_table[AMOUNT_TOKEN];
extern struct table_token fnc[AMOUNT_TOKEN];

/* Prototypes des fonctions */
Tree* new_tree(const char* x);
void clean_tree(Tree* tr);
void clean_noeud(Tree* tr);
Tree* join(Tree* left, Tree* right, const char* node);
int count_tree_nodes(Tree* tr);
Tree* to_tree(List list);
int found_element(Tree* tr, const char* elt);

List In2post2(const char* ex);
List In2post(const uint8_t* ex, unsigned str_len);
string Post2in(Tree* tr, struct table_token* tb);
int tokens(const char* s, struct table_token* w);

double Eval(Tree* tr);
bool isconstant(Tree* tr);
bool is_negation(Tree* u);
bool is_symbolic(Tree* tr);
double tonumber(const char* ex);
string tostr(double n);

Tree* remplace_tree(Tree* tr, const char* el, Tree* new_el);
Tree* remplace_var(Tree* tr, const char* el, Tree* new_el);
Tree* substitute(Tree* tr, Tree* av, Tree* ap);
bool  tree_compare(Tree* tr1, Tree* tr2);
Tree* clone(Tree* tr);
int nb_operand(Tree* tr);
Tree* operand(Tree* tr, int i);
List getvars(Tree* tr, List vrs);
string variable(Tree* u);

/* 
	-----------------------------------------------------------------------------------------------------------------------------------------------
															MAP : liste pour Tree* 
	-----------------------------------------------------------------------------------------------------------------------------------------------

*/

typedef List map;

/*-----------------------------------*/

map push_front_map(map li, Tree* tr);
map push_back_map(map li, Tree* arb);
map pop_back_map(map li);
map pop_front_map(map li);
map clear_map(map li);
map clone_map(map Li);
map map_create(Tree* tr);
map map_create_add(Tree* tr);
map map_create_prod(Tree* tr);
map map_sort(map li);
map map_remplace(map L, int pos, Tree* tr);

typedef map(ProcessFunction)(map, Tree*);
typedef map(*process_func)(map li, Tree* node);
/* 
	-----------------------------------------------------------------------------------------------------------------------------------------------
																		Simplification 
	-----------------------------------------------------------------------------------------------------------------------------------------------
*/

extern bool ALG_EXPAND;
extern bool LN_EXP_EXPAND;
extern bool TRIG_EXPAND;
extern bool RT_SIMP;
extern bool INTEGRATE;

typedef struct Trigo_value
{
	const char* angle;
	const char* cos_value;
	const char* sin_value;
	const char* tan_value;
} Trigo_value;

bool ispoly(Tree* u, const char* vr);
bool is_int(Tree* u);
bool isdemi(Tree* tr);
char* factoriel(int a);
Tree* PGCD(Tree* A, Tree* B);
Tree* pow_transform(Tree* u);

Tree* numerator_fun(Tree* u);
Tree* denominator_fun(Tree* u);
Tree* expand(Tree* tr);
Tree* factorn(int val);

bool ordre_tree(Tree* u, Tree* v);
map map_sort(map li);
Tree* simplify(Tree* u);
Tree* rationalize_expression(Tree* u);
Tree* Contract_pow(Tree* v);
Tree* algebraic_expand(Tree* u);

typedef Number(NumberOperation)(Number, Number);

/* 
	-----------------------------------------------------------------------------------------------------------------------------------------------
																	Polynomial
	-----------------------------------------------------------------------------------------------------------------------------------------------
*/

bool ismonomial(Tree* u, const char* x);
Tree* degree_sv(Tree* u, const char* x);
Tree* coefficient_gpe(Tree* u, const char* x, unsigned j);
map poly_quotient(map u, map v, token tk);
Tree* polyreconstitute(map* Li, const char* x);
map polynomial_division(map* u, map* v, map* rem);
map polycoeffs(Tree* u, const char* x);
map poly_gcd(map u, map v);
Tree* poly_simp(map u, map v, const char* x);
map polycoeffs(Tree* u, const char* x);
Tree* pfactor(map coefs, const char* x);

/*
	-----------------------------------------------------------------------------------------------------------------------------------------------
															Derivative and Integral
	-----------------------------------------------------------------------------------------------------------------------------------------------
*/

#define AMOUNT_DERIV 18

#define AMOUNT_INTEGRAL 36
#define AMOUNT_INTEGRAL_ALGX2 9
#define AMOUNT_INTEGRAL_ALGX3 12
#define AMOUNT_INTEGRAL_ALGX4 14
#define AMOUNT_INTEGRAL_ALGXN 9
#define AMOUNT_INTEGRAL_ALGX22 17
#define AMOUNT_INTEGRAL_SQRT 34
#define AMOUNT_INTEGRAL_SQRTX2 40
#define AMOUNT_INTEGRAL_SQRTX22 20
#define AMOUNT_INTEGRAL_COS 22
#define AMOUNT_INTEGRAL_SIN 22
#define AMOUNT_INTEGRAL_TRIG 49
#define AMOUNT_INTEGRAL_LN 30
#define AMOUNT_INTEGRAL_EXP 20
#define AMOUNT_INTEGRAL_INVTRIG 39
#define AMOUNT_INTEGRAL_COSH 22
#define AMOUNT_INTEGRAL_SINH 18
#define AMOUNT_INTEGRAL_TRIGH 31
#define AMOUNT_INTEGRAL_INVTRIGH 30

typedef struct FunctionFlags
{
	bool i_exp;
	bool i_ln;
	bool i_sin;
	bool i_cos;
	bool i_sqrt;
	bool i_cosh;
	bool i_sinh;
	bool i_itrigh;
	bool i_itrig;
} FunctionFlags;


typedef struct Integral
{
	const char* from;
	const char* to;
	const char* condition;
} Integral;

extern struct Integral Integraltable[];
extern struct Integral Integralalgx2[];
extern struct Integral Integralalgx3[];
extern struct Integral Integralalgx4[];
extern struct Integral IntegralalgxN[];
extern struct Integral Integralalgx22[];
extern struct Integral Integralsqrt[];
extern struct Integral Integralsqrt_X2[];
extern struct Integral Integralsqrt_X22[];
extern struct Integral Integralln[];
extern struct Integral Integralexp[];
extern struct Integral Integralsin[];
extern struct Integral Integralcos[];
extern struct Integral Integralinvtrig[];
extern struct Integral Integralinvtrigh[];
extern struct Integral Integralsinh[];
extern struct Integral Integralcosh[];
extern struct Integral Integraltrig[];
extern struct Integral Integraltrigh[];

Tree* diff(Tree* u, const char* x);
Tree* integral(Tree* f, const char* x);

/* 
	-----------------------------------------------------------------------------------------------------------------------------------------------
																			Calcul : analyse
	-----------------------------------------------------------------------------------------------------------------------------------------------
*/

extern List Error;

typedef struct Help
{
	const char* utility;
	const char* example0;
	const char* example1;
	const char* example2;
} Help;

extern const char* err_msg[];

Tree* taylor(Tree* u, Tree* vr, Tree* ordre, Tree* point);
Tree* solve_ode_2(Tree* a, Tree* b, Tree* c, Tree* f, const char* x, const char* y, Tree* cond1, Tree* cond2);
Tree* solve_ode(Tree* M, Tree* N, Tree* f, const char* x, const char* y, Tree* cond);
Tree* analyse(Tree* tr);

#endif // !__INCLUDES__H__
