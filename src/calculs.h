#include "simplify.h"

extern DList Error;

typedef struct Help
{
    const char* utility;
    const char* example0;
    const char* example1;
    const char* example2;
} Help;

Tree* analyse(Tree* tr);
