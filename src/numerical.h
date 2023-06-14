#include "dlist.h"

#define max(a,b) (a > b) ? a : b

typedef struct Number
{
	int signe;
	char* nombre;
}Number;

Number create(int signe, const char* nbr);
void free_Number(Number nbr);
char* zero_untile(const char* a);
Number sub(Number left, Number right);
Number add(Number left, Number right);
Number prod(Number left, Number right);
Number gcd(Number num, Number denom);
Number int_divid(Number num, Number denom, Number* rem);
Number divid(Number num, Number denom);
Number Logarithme(Number x);
Number Exponentiel(Number x);
Number ExponentiationRapide(Number base, Number exposant);
