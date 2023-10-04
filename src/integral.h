#include "simplify.h"

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
map polycoeffs(Tree* u, const char* x);
Tree* integral(Tree* f, const char* x);
Tree* pfactor(map coefs, const char* x);
