#include "simplify.h"

typedef struct Integral
{
	const char* expr;
	const char* calc;
	const char* condt;
} Integral;

#define trig_tok(tk) (COS_F <= tk && tk <= ATANH_F)
extern struct Integral Integraltable[];

Tree* diff(Tree* u, const char* x);
map polycoeffs(Tree* u, const char* x);
Tree* integral(Tree* f, const char* x);
Tree* square_free_factor(Tree* u, const char* x);