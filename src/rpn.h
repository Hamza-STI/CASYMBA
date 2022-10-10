#ifndef __RPN__H__
#define __RPN__H__

	#include "dlist.h"
	#include <math.h>

	#define AMONT_VALUE_TRIG 15

	typedef enum token
	{
		NUMBER, VARIABLE, UNDEF, IMAGE, PI,
		/* OPÉRATEUR */
		ADD, SUB, PROD, DIVID, POW, SEPARATEUR, PAR_OUVRANT, PAR_FERMANT,
		/* COMPARATEUR */
		EGAL, DIFFERENT, INFERIEUR, INFERIEUR_EGAL, SUPERIEUR, SUPERIEUR_EGAL,
		/* LOGIQUE */
		LOGIC_AND, LOGIC_OR,
		/* NEGATION */
		NEGATIF,
		/* FONCTION */
		EXP_F, SQRT_F, LN_F, LOG_F, LOGBASE_F, COS_F, SIN_F, TAN_F, ASIN_F,
		ACOS_F, ATAN_F, SINH_F, ASINH_F, COSH_F, ACOSH_F, TANH_F, ATANH_F,
		ROOT_F, ABS_F, SIGN_F, FACTORIEL_F,
		/* COMPLEX FONCTION */
		CONJ_F, REEL_F, IMAGE_F, ANGLE_F,
		/* FONCTION CALCULS */
		DERIV_F, LIMIT_F, INTEGRAL_F, DESOLVE_F, TANG_F, POLYROOT_F, GCD_F, INT_F,
		REMAINDER_F, FACTOR_F, EXPAND_F, COMDENOM_F, TAYLOR_F,

		/* taille enum / invalid */
		AMOUNT_TOKEN, TOKEN_INVALID
	}token;

	typedef struct table_token
	{
		string ex;
		token tok;
	}table_token;

	static const table_token fnc[AMOUNT_TOKEN] =
	{
		{ "\0", NUMBER}, { "\0", VARIABLE}, { "undef", UNDEF}, {"@i", IMAGE}, {"PI", PI},
		/* OPÉRATEUR */
		{ "+", ADD}, { "-", SUB}, { "*", PROD}, { "/", DIVID}, { "^", POW}, { ",", SEPARATEUR}, { "(", PAR_OUVRANT}, { ")", PAR_FERMANT}, 
		/* COMPARATEUR*/
		{"=", EGAL}, {"!=", DIFFERENT}, {"<", INFERIEUR}, {"<=", INFERIEUR_EGAL}, {">", SUPERIEUR}, {">=", SUPERIEUR_EGAL},
		/* LOGIQUE */
		{ "and", LOGIC_AND}, { "or", LOGIC_OR},
		/* NEGATION */
		{"~", NEGATIF},
		/* FONCTION */
		{ "exp(", EXP_F}, { "sqrt(", SQRT_F}, { "ln(", LN_F}, { "log(", LOG_F}, { "logbase(", LOGBASE_F}, { "cos(", COS_F}, {"sin(", SIN_F}, { "tan(", TAN_F}, 
		{ "asin(", ASIN_F}, { "acos(",ACOS_F}, { "atan(", ATAN_F}, { "sinh(", SINH_F}, { "asinh(", ASINH_F}, { "cosh(", COSH_F}, { "acosh(", ACOSH_F}, 
		{"tanh(", TANH_F}, { "atanh(", ATANH_F}, { "root(", ROOT_F}, { "abs(", ABS_F}, { "sign(", SIGN_F}, { "!", FACTORIEL_F},
		/* COMPLEX FUNCTION */
		{ "conj(", CONJ_F}, {"real(", REEL_F}, {"image(", IMAGE_F}, { "angle(", ANGLE_F},
		/* FONCTION CALCULS */
		{ "diff(", DERIV_F}, { "limit(", LIMIT_F}, { "integral(", INTEGRAL_F}, { "desolve(", DESOLVE_F}, { "tangent(", TANG_F},
		{"polyroots(", POLYROOT_F}, { "polygcd(", GCD_F}, { "polyquot(", INT_F}, { "polyrem(", REMAINDER_F},
		{ "factor(", FACTOR_F}, { "expand(", EXPAND_F}, {"comdenom(", COMDENOM_F}, {"taylor(", TAYLOR_F}
	};

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
		string value;
		struct Tree* tleft;
		struct Tree* tright;
		struct Tree* parent;
		optype gtype;
		token tok_type;
	}Tree;

	/* public functions */
	Tree* new_tree(const char* x);
	void clean_tree(Tree* tr);
	void clean_noeud(Tree* tr);
	Tree* join(Tree* left, Tree* right, const char* node);
	void print_tree_prefix(Tree* tr);
	int count_tree_nodes(Tree* tr);
	Tree* to_tree(DList list);
	int found_element(Tree* tr, const char* elt);

	int isop(const char* s);
	DList In2post(const char* ex);
	string Post2in(Tree* tr);
	double Eval(Tree* tr);

	Tree* remplace_tree(Tree* tr, const char* v, Tree* u);
	Tree* substitute(Tree* tr, Tree* av, Tree* ap);
	int   tree_compare(Tree* tr1, Tree* tr2);
	Tree* clone(Tree* tr);
	int  nb_operand(Tree* tr);
	Tree* operand(Tree* tr, int i);
	DList getvars(Tree* tr, DList vrs);
	string variable(Tree* u);
	int isconstant(Tree* tr);
	bool is_symbolic(Tree* tr);
	double tonumber(const char* ex);
	string tostr(double n);

#endif
