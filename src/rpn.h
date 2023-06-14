#ifndef __RPN__H__
#define __RPN__H__

	#include "numerical.h"
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

	typedef struct table_token
	{
		char ex[10];
		int length;
	}table_token;


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

	bool isnumeric(uint8_t b);
	bool isvar(uint8_t b);

	extern struct table_token ti_table[AMOUNT_TOKEN];
	extern struct table_token fnc[AMOUNT_TOKEN];

	/* Prototypes des fonctions */
	Tree* new_tree(const char* x);
	void clean_tree(Tree* tr);
	void clean_noeud(Tree* tr);
	Tree* join(Tree* left, Tree* right, const char* node);
	int count_tree_nodes(Tree* tr);
	Tree* to_tree(DList list);
	int found_element(Tree* tr, const char* elt);

	int isop(const char* s);
	DList In2post2(const char* ex);
	string Post2in2(Tree* tr);
	DList In2post(const uint8_t* ex, unsigned str_len);
	string Post2in(Tree* tr);

	double Eval(Tree* tr);
	int isconstant(Tree* tr);
    bool is_negation(Tree* u);
    bool is_symbolic(Tree* tr);
	double tonumber(const char* ex);
	string tostr(double n);

	Tree* remplace_tree(Tree* tr, const char* el, Tree* new_el);
	Tree* remplace_var(Tree* tr, const char* el, Tree* new_el);
	Tree* substitute(Tree* tr, Tree* av, Tree* ap);
	int   tree_compare(Tree* tr1, Tree* tr2);
	Tree* clone(Tree* tr);
	int nb_operand(Tree* tr);
	Tree* operand(Tree* tr, int i);
	DList getvars(Tree* tr, DList vrs);
    string variable(Tree* u);

#endif

