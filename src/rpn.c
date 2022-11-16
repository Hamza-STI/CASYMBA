#include "rpn.h"

/* private functions */
//static int isfn(const char* s);
static int tokens(const char* s);
static int token_ti(const char* s);
static int opless(const char* a, const char* b);
static int prior(const char* s);
static int nparts(DList rpn);
static DList Parts(DList rpn, int nb);


struct table_token ti_table[AMOUNT_TOKEN] =
{
	{{0}, 0}, {{0}, 0}, {{0}, 0}, {{0x2C}, 1}, {{0xAC}, 1},  {{0x0C}, 1}, {{0x0D}, 1}, {{0x0F}, 1},
	/* OPERATOR */
	{{0x10}, 1}, {{0x11}, 1}, {{0x70}, 1}, {{0x71}, 1}, {{0x82}, 1}, {{0x83}, 1}, {{0xF0}, 1}, {{0xEF, 0x2E}, 2}, {{0x2B}, 1},
	/* COMPARISON */
	{{0x6A}, 1}, {{0x6F}, 1}, {{0x6B}, 1}, {{0x6D}, 1}, {{0x6C}, 1}, {{0x6E}, 1},
	/* LOGIC */
	{{0x40}, 1}, {{0x3C}, 1},
	/* NEGATION */
	{{0xB0}, 1},
	/* FUNCTIONS */
	{{0xBF}, 1}, {{0xBC}, 1}, {{0xBD}, 1}, {{0xBE}, 1}, {{0xC0}, 1},{{0xEF, 0x34}, 2}, {{0xC1}, 1},
	{{0xB2}, 1}, {{'S', 'I', 'G', 'N', 0x10}, 5}, {{0xC4}, 1}, {{0xC2}, 1}, {{0xC6}, 1}, {{0xC3}, 1},
	{{0xC5}, 1}, {{0xC7}, 1}, {{0xC8}, 1}, {{0xC9}, 1}, {{0xCA}, 1}, {{0xCB}, 1}, {{0xCC}, 1},
	{{0xCD}, 1}, {{0x2D}, 1}, {{0xF1}, 1},
	/*COMPLEX FUNCTIONS */
	{{0xBB, 0x25}/*conj(*/, 2}, {{0xBB, 0x26}/*real(*/, 2}, {{0xBB, 0x27}/*image(*/, 2}, {{0xBB, 0x28}/*angle(*/, 2},
	/* ANALYSE FUNCTIONS */
	{{0x25}, 1}, {{0x24}, 1}, {{0x22} /*solve(*/, 1}, {{0xA7}, 1}, {{0xEF, 0x32}, 2},
	{{0xB1}, 1}, {{0xBB, 0x09}, 2}, {{0xBB, 0x2A}/*expr(*/, 2}, {{0xBB, 0x0D}/*stdDev(*/, 2}, {{0xB4}/*identity(*/, 1}, {{0xB3}/*det(*/, 1}
};

struct table_token fnc[AMOUNT_TOKEN] =
{
	{ "\0", 0}, { "\0", 0}, { "UNDEF", 5}, { "@i", 2}, { "PI", 2}, { "^(-1)", 5}, { "^2", 2}, { "^3", 2},
	/* OPÉRATEUR */
	{ "(", 1}, { ")", 1}, { "+", 1}, { "-", 1}, { "*", 1}, { "/", 1}, { "^", 1}, { "/", 1}, { ",", 1},
	/* COMPARISON */
	{ "=", 1}, { "!=", 2}, { "<", 1}, { "<=", 2}, { ">", 1}, { ">=", 2},
	/* LOGIC */
	{ "and", 3}, { "or", 2},
	/* NEGATION */
	{ "~", 1},
	/* FUNCTIONS */
	{ "exp(", 4}, { "sqrt(", 5}, { "cbrt(", 5}, { "ln(", 3}, { "log(", 4}, { "logBASE(", 8}, { "10^(", 4},
	{ "abs(", 4}, { "sign(", 5}, { "cos(", 4}, { "sin(", 4}, { "tan(", 4}, { "asin(", 5}, { "acos(",5},
	{ "atan(", 5}, { "sinh(", 6}, { "asinh(", 7}, { "cosh(", 6}, { "acosh(", 7}, { "tanh(", 6}, { "atanh(", 7},
	{ "!", 1}, { "root(", 5},
	/* COMPLEX FUNCTION */
	{ "conj(", 5}, { "real(", 5}, { "image(", 6}, { "angle(", 6},
	/* ANALYSE FUNCTIONS */
	{ "diff(", 5}, { "integral(", 9}, { "desolve(", 8}, { "tangent(", 8}, { "polyrem(", 8},
	{ "polyquot(", 9}, {"polygcd(", 8}, {"polysimp(", 9}, { "expand(", 7}, {"factor(", 7}, { "taylor(", 7}
};

bool isnumeric(uint8_t b) { return ((0x30 <= b && b <= 0x3A) || b == '.'); }
bool isvar(uint8_t b) { return ((0x41 <= b && b < 0x5B) || ('a' <= b && b <= 'z')); }

int isconstant(Tree* tr)
{
	optype op = tr->gtype;
	if (op == ENT || op == DECIMAL)
		return 1;
	if (tr->tok_type == FACTORIEL_F || op == NEGATION || tr->tok_type == ABS_F)
		return isconstant(tr->tleft);
	if (op == VAR || op == FUNCTION)
		return 0;
	if (tr->tok_type == POW)
	{
		if (tr->tright->gtype == ENT || tr->tright->gtype == DECIMAL || (tr->tright->tok_type == NEGATIF && tr->tright->tleft->gtype == ENT))
			return isconstant(tr->tleft);
		return 0;
	}
	return isconstant(tr->tleft) && isconstant(tr->tright);
}

bool is_symbolic(Tree* tr)
{
	optype op = tr->gtype;
	if (op == VAR)
		return false;
	if (op == ENT || op == DECIMAL)
		return true;
	if (op == FUNCTION)
		return isconstant(tr->tleft);
	return isconstant(tr->tleft) && isconstant(tr->tright);
}

DList Parts(DList rpn, int nb)
{

    int i = 1, n = rpn->length;
    int k = n;
    if (nb == 0)
    {
        string ch = rpn->end->value;
        DList op = NULL;
        op = push_back_dlist(op, ch);
        return op;
    }
    while (i > 0)
    {
        k--;
        DList lf = NULL;
        lf = dlist_left(rpn, k);
        i = i + nparts(lf) - 1;
        lf = clear_dlist(lf);
    }
    if (nb == 1 && k > 1)
    	return dlist_left(rpn, k - 1);
    return dlist_sub(rpn, k, n - k);
}

int nparts(DList rpn)
{
    string chr = rpn->end->value;
	token tk = tokens(chr);
    if (ADD <= tk && tk <= LOGIC_OR && tk != PAR_FERMANT && tk != PAR_OUVRANT)
        return 2;
    else if (NEGATIF <= tk && tk < AMOUNT_TOKEN)
        return 1;
    return 0;
}

int prior(const char* s)
{
    token ch = tokens(s);
    if (NEGATIF < ch && ch < AMOUNT_TOKEN)
    	return 10;
    else if (ch == POW)
    	return 9;
    else if (ch == NEGATIF)
    	return 8;
    else if (ch == PROD || ch == DIVID)
    	return 7;
    else if (ch == ADD || ch == SUB)
    	return 6;
    else if (EGAL <= ch && ch <= SUPERIEUR_EGAL)
    	return 5;
    else if (ch == LOGIC_OR)
    	return 4;
    else if (ch == LOGIC_AND)
    	return 3;
    else if (ch == SEPARATEUR)
    	return 2;
    else if (ch == PAR_FERMANT || ch == PAR_OUVRANT)
    	return 1;
    return 0;
}

int isfn(const char* s)
{
	char fch = s[0], lch = s[strlen(s) - 1];
	if ((isvar(fch) && lch == '(') || fch == '!')
		return 1;
	return 0;
}

int cisop(char ch)
{
	return ch == '+' || ch == '-' || ch == '/' || ch == '*' || ch == '^' || ch == '=' || ch == '>' || ch == '<' || ch == '(' || ch == ')' || ch == '~' || ch == ',' || ch == '!';
}

int isop(const char* s)
{
	token tk = token_ti(s);
	if (tk == TOKEN_INVALID)
		tk = tokens(s);
	return !(tk == TOKEN_INVALID);
}

int opless( const char* a, const char* b)
{
	if (a[0] != '~' && a[0] != '^')
		return prior(a) <= prior(b);
	return prior(a) < prior(b);
}

DList In2post(const uint8_t* ex, unsigned k)
{
	DList result = NULL, rlt = NULL, opstack = NULL;
	DListCell *tmp;
	char temp[TAILLE_MAX] = { 0 }, chr[3] = { 0 };
	int stklen = 0, sl, p = 0;
	unsigned i;
	temp[0] = '\0';
	for (i = 0; i < k; ++i)
	{
		uint8_t ch = ex[i];
		chr[0] = ch;
		chr[1] = '\0';
		token tk = token_ti(chr);
		sl = strlen(temp);
		if (UNDEF < tk && tk <= PI)
		{
			if (result == NULL)
				result = push_back_dlist(result, fnc[tk].ex);
			else
			{
				if (sl > 0)
				{
					int j, count = strlen(temp);
					result = push_back_dlist(result, temp);
					result = push_back_dlist(result, fnc[PROD].ex);
					for (j = 0; j < count; ++j)
						temp[j] = '\0';
				}
				else if (result != NULL)
				{
					token t = tokens(result->end->value);
					if (!(ADD <= t && t <= NEGATIF) && t != PAR_OUVRANT && t != TOKEN_INVALID)
						result = push_back_dlist(result, fnc[PROD].ex);
				}
				result = push_back_dlist(result, fnc[tk].ex);
			}
			sl = 0;
		}
		else if(ch == 0xBB || ch == 0xEF)
		{
			i++;
			char fn[3] = { ch, ex[i] };
			token tk = token_ti(fn);
			if (tk != TOKEN_INVALID)
			{
				if (sl != 0)
				{
					result = push_back_dlist(result, temp);
					if (EXP_F <= tk && tk < AMOUNT_TOKEN)
						result = push_back_dlist(result, fnc[PROD].ex);
				}
				if (result != NULL && tk != FRACTION)
				{
					token t = tokens(result->end->value);
					if (!(ADD <= t && t <= NEGATIF) && t != PAR_OUVRANT && t != TOKEN_INVALID)
						result = push_back_dlist(result, fnc[PROD].ex);
				}
				result = push_back_dlist(result, fnc[tk].ex);
				if (EXP_F <= tk && tk < AMOUNT_TOKEN)
				{
					result = push_back_dlist(result, fnc[PAR_OUVRANT].ex);
					p++;
				}
				for (int j = 0; j < sl; ++j)
					temp[j] = '\0';
				sl = 0;
			}
			else
			{
				if (result != NULL)
					result = clear_dlist(result);
				return NULL;
			}
		}
		else if (INVERSE <= tk && tk <= CUBE)
		{
			if (sl)
				result = push_back_dlist(result, temp);
			result = push_back_dlist(result, fnc[POW].ex);
			if (tk == INVERSE)
			{
				result = push_back_dlist(result, fnc[PAR_OUVRANT].ex);
				result = push_back_dlist(result, fnc[NEGATIF].ex);
				result = push_back_dlist(result, "1");
				result = push_back_dlist(result, fnc[PAR_FERMANT].ex);
			}
			else if (tk == CARRE)
				result = push_back_dlist(result, "2");
			else
				result = push_back_dlist(result, "3");
			for (int j = 0; j < sl; ++j)
				temp[j] = '\0';
			sl = 0;
		}
		else if (tk == TOK_10_POWER)
		{
			result = push_back_dlist(result, "10");
			result = push_back_dlist(result, fnc[POW].ex);
			result = push_back_dlist(result, fnc[PAR_OUVRANT].ex);
		}
		else if (!isop(chr))
		{
			if (strlen(temp) == 0)
			{
				if (result != NULL)
				{
					token t = tokens(result->end->value);
					if (t == PAR_FERMANT || t == PI || t == IMAGE || t == FACTORIEL_F)
						result = push_back_dlist(result, fnc[PROD].ex);
				}
				temp[sl] = ch;
			}
			else
			{
				if ((isvar(temp[0]) && isnumeric(ch)) || (isvar(ch) && isnumeric(temp[0])))
				{
					result = push_back_dlist(result, temp);
					result = push_back_dlist(result, fnc[PROD].ex);
					for (int j = 0; j < sl; ++j)
						temp[j] = '\0';
					sl = 0;
				}
				if (ch == 0x3A)
					ch = '.';
				temp[sl] = ch;
			}
			temp[sl + 1] = '\0';
		}
		else
		{
			if (tk == PAR_OUVRANT || (EXP_F <= tk && tk < AMOUNT_TOKEN && tk != FACTORIEL_F))
				p++;
			if (tk == PAR_FERMANT)
				p--;
			if (sl != 0)
			{
				result = push_back_dlist(result, temp);
				if (((EXP_F <= tk && tk < AMOUNT_TOKEN) || tk == PAR_OUVRANT) && tk != FACTORIEL_F)
					result = push_back_dlist(result, fnc[PROD].ex);
			}
			else if (result != NULL && tk != PAR_FERMANT && !(ADD <= tk && tk <= LOGIC_OR))
			{
				token t = tokens(result->end->value);
				if (t == PAR_FERMANT)
					result = push_back_dlist(result, fnc[PROD].ex);
			}
			if (tk == SUB)
			{
				if (result == NULL)
					tk = NEGATIF;
				else
				{
					token t = tokens(result->end->value);
					if (((ADD <= t && t <= LOGIC_OR) || t == PAR_OUVRANT))
						tk = NEGATIF;
				}
			}
			if (result == NULL && ((ADD <= tk && tk <= LOGIC_OR) || tk == PAR_FERMANT))
			{
				result = clear_dlist(result);
				return NULL;
			}
			if (result != NULL)
			{
				token t = tokens(result->end->value);
				if (((ADD <= t && t <= LOGIC_OR) && tk == PAR_FERMANT) ||
				    (((ADD <= t && t <= LOGIC_OR) || t == NEGATIF || t == PAR_OUVRANT) && (ADD <= tk && tk <= LOGIC_OR)))
				{
					result = clear_dlist(result);
					return NULL;
				}
			}
			result = push_back_dlist(result, fnc[tk].ex);
			if ((EXP_F <= tk && tk < AMOUNT_TOKEN) && tk != FACTORIEL_F)
				result = push_back_dlist(result, fnc[PAR_OUVRANT].ex);
			for (int j = 0; j < sl; ++j)
				temp[j] = '\0';
		}
	}
	sl = strlen(temp);
	if (sl != 0)
	{
		temp[sl] = '\0';
		result = push_back_dlist(result, temp);
	}
	while (p > 0)
	{
		result = push_back_dlist(result, fnc[PAR_FERMANT].ex);
		p--;
	}
	tmp = result->begin;
	while (tmp != NULL)
	{
		if (!isop(tmp->value) || !strcmp(tmp->value, fnc[PI].ex) || !strcmp(tmp->value, fnc[IMAGE].ex))
			rlt = push_back_dlist(rlt, tmp->value);
		else
		{
			if ((tmp->value)[0] != '(' && (tmp->value)[0] != ')')
			{
				while (opless(tmp->value, dlist_last(opstack)) && stklen > 0)
				{
					rlt = push_back_dlist(rlt, dlist_last(opstack));
					opstack = pop_back_dlist(opstack);
					stklen--;
				}
			}
			if ((tmp->value)[0] == ')')
			{
				while (dlist_last(opstack)[0] != '(')
				{
					rlt = push_back_dlist(rlt, dlist_last(opstack));
					opstack = pop_back_dlist(opstack);
					stklen--;
				}
				opstack = pop_back_dlist(opstack);
				stklen--;
			}
			if ((tmp->value)[0] != ')')
			{
				opstack = push_back_dlist(opstack, tmp->value);
				stklen++;
			}
		}
		tmp = tmp->next;
	}
	while (opstack != NULL)
	{
		rlt = push_back_dlist(rlt, opstack->end->value);
		opstack = pop_back_dlist(opstack);
	}
	result = clear_dlist(result);
	opstack = clear_dlist(opstack);
	return rlt;
}

DList In2post2(const char* ex)
{
	DList result = NULL;
	char ch, tch;
	char temp[TAILLE_MAX] = { 0 }, op[2] = { 0 };
	int sl = 0, p = 0;
	for (unsigned int i = 0; i < strlen(ex); ++i)
	{
		ch = ex[i];
		if (ch == ' ')
		{
			if (sl)
				result = push_back_dlist(result, temp);
			for (int k = sl - 1; k >= 0; k--)
				temp[k] = '\0';
			sl = 0;
		}
		else if (!cisop(ch))
		{
			if (sl && ((isvar(ch) && isnumeric(temp[sl - 1])) || (isnumeric(ch) && isvar(temp[sl - 1]))))
			{
				result = push_back_dlist(result, temp);
				result = push_back_dlist(result, fnc[PROD].ex);
				for (int k = sl - 1; k >= 0; k--)
					temp[k] = '\0';
				sl = 0;
			}
			temp[sl] = ch;
			temp[sl + 1] = '\0';
			if (!strcmp(temp, fnc[PI].ex) || !strcmp(temp, fnc[IMAGE].ex))
			{
				result = push_back_dlist(result, temp);
				for (int k = sl - 1; k >= 0; k--)
					temp[k] = '\0';
				sl = 0;
			}
			else if (!strcmp(temp, "pi"))
			{
				result = push_back_dlist(result, fnc[PI].ex);
				for (int k = sl - 1; k >= 0; k--)
					temp[k] = '\0';
				sl = 0;
			}
			else
				sl++;
		}
		else
		{
			if (ch == '(')
				p++;
			if (ch == ')')
				p--;
			if (sl)
			{
				if (ch == '(')
				{
					tch = temp[0];
					if (isvar(tch))
					{
						temp[sl] = ch;
						temp[sl + 1] = '\0';
					}
					result = push_back_dlist(result, temp);
					if (isnumeric(tch))
						result = push_back_dlist(result, fnc[PROD].ex);
				}
				else
					result = push_back_dlist(result, temp);
			}
			op[0] = ch;
			op[1] = '\0';
			token tk = tokens(op);
			if (result != NULL && tk != PAR_FERMANT && !(ADD <= tk && tk <= LOGIC_OR))
			{
				token t = tokens(result->end->value);
				if (t == PAR_FERMANT)
					result = push_back_dlist(result, fnc[PROD].ex);
			}
			if (tk == SUB)
			{
				if (result == NULL)
					tk = NEGATIF;
				else
				{
					token t = tokens(result->end->value);
					if (((ADD <= t && t <= LOGIC_OR) || t == PAR_OUVRANT))
						tk = NEGATIF;
				}
			}
			if (result == NULL && ((ADD <= tk && tk <= LOGIC_OR) || tk == PAR_FERMANT))
			{
				result = clear_dlist(result);
				return NULL;
			}
			if (result != NULL)
			{
				token t = tokens(result->end->value);
				if (((ADD <= t && t <= LOGIC_OR) && tk == PAR_FERMANT) ||
					(((ADD <= t && t <= LOGIC_OR) || t == NEGATIF || t == PAR_OUVRANT) && (ADD <= tk && tk <= LOGIC_OR)))
				{
					result = clear_dlist(result);
					return NULL;
				}
			}
			result = push_back_dlist(result, op);
			for (int k = sl - 1; k >= 0; k--)
				temp[k] = '\0';
			sl = 0;
		}
	}
	if (sl != 0)
	{
		temp[sl] = '\0';
		result = push_back_dlist(result, temp);
	}
	while (p)
	{
		result = push_back_dlist(result, fnc[PAR_FERMANT].ex);
		p--;
	}
	int stklen = 0, n = result->length;
	DList rlt = NULL;
	DList opstack = NULL;
	DListCell* tmp = result->begin;
	for (int i = 0; i < n; ++i)
	{
		if (!(cisop(tmp->value[0]) || isfn(tmp->value)))
		{
			rlt = push_back_dlist(rlt, tmp->value);
		}
		else
		{
			if ((tmp->value)[0] != '(' && (tmp->value)[0] != ')')
			{
				while (opless(tmp->value, dlist_last(opstack)) && stklen > 0)
				{
					rlt = push_back_dlist(rlt, dlist_last(opstack));
					opstack = pop_back_dlist(opstack);
					stklen--;
				}
			}
			if ((tmp->value)[0] == ')')
			{
				while (dlist_last(opstack)[0] != '(')
				{
					rlt = push_back_dlist(rlt, dlist_last(opstack));
					opstack = pop_back_dlist(opstack);
					stklen--;
				}
				opstack = pop_back_dlist(opstack);
				stklen--;
			}
			if ((tmp->value)[0] != ')')
			{
				opstack = push_back_dlist(opstack, tmp->value);
				stklen++;
			}
		}
		tmp = tmp->next;
	}
	while (opstack != NULL)
	{
		rlt = push_back_dlist(rlt, dlist_last(opstack));
		opstack = pop_back_dlist(opstack);
	}
	result = clear_dlist(result);
	opstack = clear_dlist(opstack);
	return rlt;
}

int tokens(const char* s)
{
	table_token *element;
	int k = 0;
	for (element = fnc; element != element + AMOUNT_TOKEN - 1; element++)
	{
		if (!strcmp(element->ex, s))
			return k;
		k++;
		if (k == AMOUNT_TOKEN)
			break;
	}
	return TOKEN_INVALID;
}

int token_ti(const char* s)
{
	table_token *element;
	int k = 0;
	for (element = ti_table; element != element + AMOUNT_TOKEN - 1; element++)
	{
		if (!strcmp(element->ex, s))
			return k;
		k++;
		if (k == AMOUNT_TOKEN)
			break;
	}
	return TOKEN_INVALID;
}

Tree *new_tree(const char* x)
{
	Tree *tr = malloc(sizeof(Tree));
	tr->value = strdup(x);
	token tk = tokens(x);
	if (tk != TOKEN_INVALID)
	{
		tr->parent = NULL;
		if (EXP_F <= tk && tk < AMOUNT_TOKEN)
			tr->gtype = FUNCTION;
		else
		{
			if (tk == NEGATIF)
				tr->gtype = NEGATION;
			else if (tk == LOGIC_AND || tk == LOGIC_OR)
				tr->gtype = LOGIC;
			else if (ADD <= tk && tk <= SUPERIEUR_EGAL)
				tr->gtype = OPERAT;
			else if (UNDEF <= tk && tk <= PI)
				tr->gtype = VAR;
		}
		tr->tok_type = tk;
	}
	else
	{
		tr->parent = NULL;
		if (isnumeric(x[0]))
		{
			char *id = strchr(x, '.');
			if (id == NULL)
				tr->gtype = ENT;
			else
				tr->gtype = DECIMAL;
			tr->tok_type = NUMBER;
		}
		else
		{
			tr->tok_type = VARIABLE;
			tr->gtype = VAR;
		}
	}
	tr->tleft = NULL;
	tr->tright = NULL;
	return tr;
}

void clean_tree(Tree *tr)
{
	if(tr == NULL)
		return;

	clean_tree(tr->tleft);
	clean_tree(tr->tright);
	free(tr->value);
	free(tr);
}

void clean_noeud(Tree *tr)
{
	if(tr == NULL)
		return;
	free(tr->value);
	free(tr);
}

Tree *join(Tree *left, Tree *right, const char* node)
{
	Tree *tr = new_tree(node);

	tr->tleft = left;
	tr->tright = right;

	if(left != NULL)
		left->parent = tr;
	if(right != NULL)
		right->parent = tr;

	return tr;
}

int count_tree_nodes(Tree *tr)
{
	if(tr == NULL)
		return 0;

	return (count_tree_nodes(tr->tleft) + count_tree_nodes(tr->tright) + 1);
}

Tree *to_tree(DList list)
{
	string ch = list->end->value;
	int n = nparts(list);
	Tree *tr = NULL;
	if (n == 2)
		tr = join(to_tree(Parts(list , 1)), to_tree(Parts(list , 2)), ch);
	else if (n == 1)
		tr = join(to_tree(Parts(list , 1)), NULL, ch);
	else
		tr = new_tree(ch);
	clear_dlist(list);
	return tr;
}

int found_element(Tree *tr, const char* elt)
{
	if (tr == NULL || (strcmp(tr->value, elt) && tr->tleft == NULL))
		return 0;
	if (!strcmp(tr->value, elt))
		return 1;
	return found_element(tr->tleft, elt) || found_element(tr->tright, elt);
}

double tonumber(const char* ex)
{
    if (strchr(ex, (int)0x3A) == NULL && strchr(ex, '.') == NULL )
    {
        return atoi(ex);
    }
	return strtod(ex, NULL);
}

string tostr(double t)
{
	static char ex[50];
	double ent;
	double dec = modf(t, &ent);
	if (!dec)
		snprintf(ex, 50, "%d", (int)t);
	else
    {
        snprintf(ex, 50, "%0.9f", t);
        int k = strlen(ex) - 1;
        while (ex[k] == '0')
        {
            ex[k] = '\0';
            k--;
        }
    }
	return ex;
}

DList Post2in_rec(Tree* tr, DList rec)
{
	optype op = tr->gtype;
	if (op <= VAR)
	{
		if (tr->tok_type == PI || tr->tok_type == IMAGE)
			rec = push_back_dlist(rec, ti_table[tr->tok_type].ex);
		else if (op == DECIMAL)
		{
			size_t t = strlen(tr->value);
			for (unsigned int i = 0; i < t; ++i)
			{
				if (tr->value[i] == '.')
				{
					tr->value[i] = 0x3A;
				}
			}
			rec = push_back_dlist(rec, tr->value);
		}
		else
			rec = push_back_dlist(rec, tr->value);
		return rec;
	}
	if (op == FUNCTION)
	{
		rec = Post2in_rec(tr->tleft, rec);
		if (tr->tok_type == FACTORIEL_F)
		{
			string tmp = malloc((strlen(rec->end->value) + ti_table[tr->tok_type].length + 1) * sizeof(tmp));
			if (tr->tleft->gtype == OPERAT)
				sprintf(tmp, "%s%s%s%s", ti_table[PAR_OUVRANT].ex, rec->end->value, ti_table[PAR_FERMANT].ex, ti_table[tr->tok_type].ex);
			else
				sprintf(tmp, "%s%s", rec->end->value, ti_table[tr->tok_type].ex);
			rec = pop_back_dlist(rec);
			rec = push_back_dlist(rec, tmp);
			free(tmp);
			return rec;
		}
		string tmp = malloc((strlen(rec->end->value) + ti_table[tr->tok_type].length + 1) * sizeof(tmp));
		sprintf(tmp, "%s%s%s", ti_table[tr->tok_type].ex, rec->end->value, ti_table[PAR_FERMANT].ex);
		rec = pop_back_dlist(rec);
		rec = push_back_dlist(rec, tmp);
		free(tmp);
		return rec;
	}
	else if (op == OPERAT)
	{
		token sig = tr->tok_type;
		rec = Post2in_rec(tr->tleft, rec);
		rec = Post2in_rec(tr->tright, rec);
		string pleft = rec->end->back->value;
		string pright = rec->end->value;
		string oper = ti_table[sig].ex;
		if (sig == SUB)
		{
			string tmp = malloc((strlen(pleft) + strlen(pright) + 3) * sizeof(tmp));
			if (tr->tright->tleft != NULL && (tr->tright->tok_type == ADD || tr->tright->tok_type == SUB))
				sprintf(tmp, "%s%s%s%s%s", pleft, oper, ti_table[PAR_OUVRANT].ex, pright, ti_table[PAR_FERMANT].ex);
			else
				sprintf(tmp, "%s%s%s", pleft, oper, pright);
			rec = pop_back_dlist(rec);
			rec = pop_back_dlist(rec);
			rec = push_back_dlist(rec, tmp);
			free(tmp);
			return rec;
		}
		else if (sig == PROD)
		{
			if (!strcmp(pleft, "1"))
			{
				rec = dlist_remove_id(rec, rec->length - 1);
				return rec;
			}
			if (!strcmp(pright, "1"))
			{
				rec = pop_back_dlist(rec);
				return rec;
			}
			string tmp = malloc((strlen(pleft) + strlen(pright) + 7) * sizeof(tmp));
			string tmp1 = malloc((strlen(pright) + 3) * sizeof(tmp1));
			if (tr->tleft->tleft != NULL && (tr->tleft->tok_type == ADD || tr->tleft->tok_type == SUB))
				sprintf(tmp1, "%s%s%s%s", ti_table[PAR_OUVRANT].ex, pleft, ti_table[PAR_FERMANT].ex, oper);
			else
				sprintf(tmp1, "%s%s", pleft, oper);
			if (tr->tright->tleft != NULL && (tr->tright->tok_type == ADD || tr->tright->tok_type == SUB))
				sprintf(tmp, "%s%s%s%s", tmp1, ti_table[PAR_OUVRANT].ex, pright, ti_table[PAR_FERMANT].ex);
			else
				sprintf(tmp, "%s%s", tmp1, pright);
			rec = pop_back_dlist(rec);
			rec = pop_back_dlist(rec);
			rec = push_back_dlist(rec, tmp);
			free(tmp); free(tmp1);
			return rec;
		}
		else if (sig == DIVID)
		{
			if (!strcmp(pright, "1"))
			{
				rec = pop_back_dlist(rec);
				return rec;
			}
			string tmp = malloc((strlen(pleft) + strlen(pright) + ti_table[FRACTION].length + 4 * ti_table[PAR_OUVRANT].length + 1) * sizeof(tmp));
			string tmp1 = malloc((strlen(pleft) + ti_table[FRACTION].length + 2 * ti_table[PAR_OUVRANT].length + 1) * sizeof(tmp1));
			if (tr->tleft->tleft != NULL && (ADD <= tr->tleft->tok_type && tr->tleft->tok_type <= PROD))
				sprintf(tmp1, "%s%s%s%s", ti_table[PAR_OUVRANT].ex, pleft, ti_table[PAR_FERMANT].ex, ti_table[FRACTION].ex);
			else
				sprintf(tmp1, "%s%s", pleft, ti_table[FRACTION].ex);
			if (tr->tright->tleft != NULL && (ADD <= tr->tright->tok_type && tr->tright->tok_type <= POW))
				sprintf(tmp, "%s%s%s%s", tmp1, ti_table[PAR_OUVRANT].ex, pright, ti_table[PAR_FERMANT].ex);
			else
				sprintf(tmp, "%s%s", tmp1, pright);
			rec = pop_back_dlist(rec);
			rec = pop_back_dlist(rec);
			rec = push_back_dlist(rec, tmp);
			free(tmp); free(tmp1);
			return rec;
		}
		else if (sig == POW)
		{
			if (!strcmp(pright, "1"))
			{
				rec = pop_back_dlist(rec);
				return rec;
			}
			string tmp = malloc((strlen(pleft) + strlen(pright) + 7) * sizeof(tmp));
			string tmp1 = malloc((strlen(pleft) + 3) * sizeof(tmp1));
			if (tr->tleft->tleft != NULL && ((ADD <= tr->tleft->tok_type && tr->tleft->tok_type <= POW) || tr->tleft->tok_type == NEGATIF))
				sprintf(tmp1, "%s%s%s%s", ti_table[PAR_OUVRANT].ex, pleft, ti_table[PAR_FERMANT].ex, oper);
			else
				sprintf(tmp1, "%s%s", pleft, oper);
			if (tr->tright->tleft != NULL && ((ADD <= tr->tright->tok_type && tr->tright->tok_type <= POW) || tr->tright->tok_type == NEGATIF))
				sprintf(tmp, "%s%s%s%s", tmp1, ti_table[PAR_OUVRANT].ex, pright, ti_table[PAR_FERMANT].ex);
			else
				sprintf(tmp, "%s%s", tmp1, pright);
			rec = pop_back_dlist(rec);
			rec = pop_back_dlist(rec);
			rec = push_back_dlist(rec, tmp);
			free(tmp); free(tmp1);
			return rec;
		}
		else
		{
			string tmp = malloc((strlen(pleft) + strlen(pright) + 1) * sizeof(tmp));
			if (sig == ADD && pright[0] == (char)0xB0)
			{
				pright[0] = ti_table[SUB].ex[0];
				sprintf(tmp, "%s%s", pleft, pright);
			}
			else
				sprintf(tmp, "%s%s%s", pleft, oper, pright);
			rec = pop_back_dlist(rec);
			rec = pop_back_dlist(rec);
			rec = push_back_dlist(rec, tmp);
			free(tmp);
			return rec;
		}
	}
	else if (op == LOGIC)
	{
		rec = Post2in_rec(tr->tleft, rec);
		rec = Post2in_rec(tr->tright, rec);
		string pleft = rec->end->back->value;
		string pright = rec->end->value;
		string oper = ti_table[tr->tok_type].ex;
		string tmp = malloc((strlen(pleft) + strlen(pright) + strlen(tr->value) + 2) * sizeof(tmp));
		sprintf(tmp, "%s%s%s", pleft, oper, pright);
		rec = pop_back_dlist(rec);
		rec = pop_back_dlist(rec);
		rec = push_back_dlist(rec, tmp);
		free(tmp);
		return rec;
	}
	else
	{
		rec = Post2in_rec(tr->tleft, rec);
		if (tr->tleft->tleft != NULL)
		{
			token sigt = tr->tleft->tok_type;
			if (sigt == ADD || sigt == SUB)
			{
				string tmp = malloc((strlen(rec->end->value) + 3) * sizeof(tmp));
				sprintf(tmp, "%s%s%s%s", ti_table[NEGATIF].ex, ti_table[PAR_OUVRANT].ex, rec->end->value, ti_table[PAR_FERMANT].ex);
				rec = pop_back_dlist(rec);
				rec = push_back_dlist(rec, tmp);
				free(tmp);
				return rec;
			}
		}
		string tmp = malloc((strlen(rec->end->value) + 1) * sizeof(tmp));
		sprintf(tmp, "%s%s", ti_table[NEGATIF].ex, rec->end->value);
		rec = pop_back_dlist(rec);
		rec = push_back_dlist(rec, tmp);
		free(tmp);
		return rec;
	}
}

string Post2in(Tree* tr)
{
	DList rec = NULL;
	DList r_str = Post2in_rec(tr, rec);
	static char ex[TAILLE_MAX];
	strcpy(ex, r_str->end->value);
	ex[strlen(r_str->end->value)] = '\0';
	r_str = clear_dlist(r_str);
	return ex;
}

DList Post2in2_rec(Tree* tr, DList rec)
{
	optype op = tr->gtype;
	if (op <= VAR)
	{
		if(op == DECIMAL)
        {
            size_t t = strlen(tr->value);
            for (unsigned int i = 0; i < t; ++i)
            {
                if (tr->value[i] == '.')
                {
                    tr->value[i] = 0x3A;
                }
            }
            rec = push_back_dlist(rec, tr->value);
        }
        else
			rec = push_back_dlist(rec, tr->value);
		return rec;
	}
	if (op == FUNCTION)
	{
        rec = Post2in2_rec(tr->tleft, rec);
        if (tr->tok_type == FACTORIEL_F)
        {
            string tmp = malloc((strlen(rec->end->value) + fnc[tr->tok_type].length + 1) * sizeof(tmp));
            if (tr->tleft->gtype == OPERAT)
                sprintf(tmp, "%s%s%s%s", fnc[PAR_OUVRANT].ex, rec->end->value, fnc[PAR_FERMANT].ex, fnc[tr->tok_type].ex);
            else
                sprintf(tmp, "%s%s", rec->end->value, fnc[tr->tok_type].ex);
            rec = pop_back_dlist(rec);
            rec = push_back_dlist(rec, tmp);
            free(tmp);
            return rec;
        }
		string tmp = malloc((strlen(rec->end->value) + fnc[tr->tok_type].length + 1) * sizeof(tmp));
		sprintf(tmp, "%s%s%s", fnc[tr->tok_type].ex, rec->end->value, fnc[PAR_FERMANT].ex);
		rec = pop_back_dlist(rec);
		rec = push_back_dlist(rec, tmp);
		free(tmp);
		return rec;
	}
	else if (op == OPERAT)
	{
		token sig = tr->tok_type;
		rec = Post2in2_rec(tr->tleft, rec);
		rec = Post2in2_rec(tr->tright, rec);
		string pleft = rec->end->back->value;
		string pright = rec->end->value;
		string oper = fnc[sig].ex;
		if (sig == SUB)
		{
			string tmp = malloc((strlen(pleft) + strlen(pright) + 3) * sizeof(tmp));
			if (tr->tright->tleft != NULL && (tr->tright->tok_type == ADD || tr->tright->tok_type == SUB))
				sprintf(tmp, "%s%s%s%s%s", pleft, oper, fnc[PAR_OUVRANT].ex, pright, fnc[PAR_FERMANT].ex);
			else
				sprintf(tmp, "%s%s%s", pleft, oper, pright);
			rec = pop_back_dlist(rec);
			rec = pop_back_dlist(rec);
			rec = push_back_dlist(rec, tmp);
			free(tmp);
			return rec;
		}
		else if (sig == PROD)
		{
            if (!strcmp(pleft, "1"))
			{
				rec = dlist_remove_id(rec, rec->length - 1);
				return rec;
			}
			if (!strcmp(pright, "1"))
			{
				rec = pop_back_dlist(rec);
				return rec;
			}
			string tmp = malloc((strlen(pleft) + strlen(pright) + 7) * sizeof(tmp));
			string tmp1 = malloc((strlen(pright) + 3) * sizeof(tmp1));
			if (tr->tleft->tleft != NULL && (tr->tleft->tok_type == ADD || tr->tleft->tok_type == SUB))
				sprintf(tmp1, "%s%s%s%s", fnc[PAR_OUVRANT].ex, pleft, fnc[PAR_FERMANT].ex, oper);
			else
				sprintf(tmp1, "%s%s", pleft, oper);
			if (tr->tright->tleft != NULL && (tr->tright->tok_type == ADD || tr->tright->tok_type == SUB))
				sprintf(tmp, "%s%s%s%s", tmp1, fnc[PAR_OUVRANT].ex, pright, fnc[PAR_FERMANT].ex);
			else
				sprintf(tmp, "%s%s", tmp1, pright);
			rec = pop_back_dlist(rec);
			rec = pop_back_dlist(rec);
			rec = push_back_dlist(rec, tmp);
			free(tmp); free(tmp1);
			return rec;
		}
		else if (sig == DIVID)
		{
            if (!strcmp(pright, "1"))
			{
				rec = pop_back_dlist(rec);
				return rec;
			}
			string tmp = malloc((strlen(pleft) + strlen(pright) + fnc[FRACTION].length + 4 * fnc[PAR_OUVRANT].length + 1) * sizeof(tmp));
			string tmp1 = malloc((strlen(pleft) + fnc[FRACTION].length + 2 * fnc[PAR_OUVRANT].length + 1) * sizeof(tmp1));
			if (tr->tleft->tleft != NULL && (ADD <= tr->tleft->tok_type && tr->tleft->tok_type <= PROD))
				sprintf(tmp1, "%s%s%s%s", fnc[PAR_OUVRANT].ex, pleft, fnc[PAR_FERMANT].ex, fnc[FRACTION].ex);
			else
				sprintf(tmp1, "%s%s", pleft, fnc[FRACTION].ex);
			if (tr->tright->tleft != NULL && (ADD <= tr->tright->tok_type && tr->tright->tok_type <= POW))
				sprintf(tmp, "%s%s%s%s", tmp1, fnc[PAR_OUVRANT].ex, pright, fnc[PAR_FERMANT].ex);
			else
				sprintf(tmp, "%s%s", tmp1, pright);
			rec = pop_back_dlist(rec);
			rec = pop_back_dlist(rec);
			rec = push_back_dlist(rec, tmp);
			free(tmp); free(tmp1);
			return rec;
		}
		else if (sig == POW)
		{
            if (!strcmp(pright, "1"))
			{
				rec = pop_back_dlist(rec);
				return rec;
			}
			string tmp = malloc((strlen(pleft) + strlen(pright) + 7) * sizeof(tmp));
			string tmp1 = malloc((strlen(pleft) + 3) * sizeof(tmp1));
			if (tr->tleft->tleft != NULL && ((ADD <= tr->tleft->tok_type && tr->tleft->tok_type <= POW) || tr->tleft->tok_type == NEGATIF))
				sprintf(tmp1, "%s%s%s%s", fnc[PAR_OUVRANT].ex, pleft, fnc[PAR_FERMANT].ex, oper);
			else
				sprintf(tmp1, "%s%s", pleft, oper);
			if (tr->tright->tleft != NULL && ((ADD <= tr->tright->tok_type && tr->tright->tok_type <= POW) || tr->tright->tok_type == NEGATIF))
				sprintf(tmp, "%s%s%s%s", tmp1, fnc[PAR_OUVRANT].ex, pright, fnc[PAR_FERMANT].ex);
			else
				sprintf(tmp, "%s%s", tmp1, pright);
			rec = pop_back_dlist(rec);
			rec = pop_back_dlist(rec);
			rec = push_back_dlist(rec, tmp);
			free(tmp); free(tmp1);
			return rec;
		}
		else
		{
			string tmp = malloc((strlen(pleft) + strlen(pright) + 1) * sizeof(tmp));
			if (sig == ADD && pright[0] == (char)0xB0)
			{
				pright[0] = fnc[SUB].ex[0];
				sprintf(tmp, "%s%s", pleft, pright);
			}
			else
				sprintf(tmp, "%s%s%s", pleft, oper, pright);
			rec = pop_back_dlist(rec);
			rec = pop_back_dlist(rec);
			rec = push_back_dlist(rec, tmp);
			free(tmp);
			return rec;
		}
	}
	else if (op == LOGIC)
	{
		rec = Post2in2_rec(tr->tleft, rec);
		rec = Post2in2_rec(tr->tright, rec);
		string pleft = rec->end->back->value;
		string pright = rec->end->value;
        string oper = fnc[tr->tok_type].ex;
		string tmp = malloc((strlen(pleft) + strlen(pright) + strlen(tr->value) + 2) * sizeof(tmp));
		sprintf(tmp, "%s%s%s", pleft, oper, pright);
		rec = pop_back_dlist(rec);
		rec = pop_back_dlist(rec);
		rec = push_back_dlist(rec, tmp);
		free(tmp);
		return rec;
	}
	else
	{
		rec = Post2in2_rec(tr->tleft, rec);
		if (tr->tleft->tleft != NULL)
		{
			token sigt = tr->tleft->tok_type;
			if (sigt == ADD || sigt == SUB)
			{
				string tmp = malloc((strlen(rec->end->value) + 3) * sizeof(tmp));
				sprintf(tmp, "%s%s%s%s", fnc[NEGATIF].ex, fnc[PAR_OUVRANT].ex, rec->end->value, fnc[PAR_FERMANT].ex);
				rec = pop_back_dlist(rec);
				rec = push_back_dlist(rec, tmp);
				free(tmp);
				return rec;
			}
		}
		string tmp = malloc((strlen(rec->end->value) + 1) * sizeof(tmp));
		sprintf(tmp, "%s%s", fnc[NEGATIF].ex, rec->end->value);
		rec = pop_back_dlist(rec);
		rec = push_back_dlist(rec, tmp);
		free(tmp);
		return rec;
	}
}

string Post2in2(Tree* tr)
{
	DList rec = NULL;
	DList r_str = Post2in2_rec(tr, rec);
	static char ex[TAILLE_MAX];
	strcpy(ex, r_str->end->value);
    ex[strlen(r_str->end->value)] = '\0';
	r_str = clear_dlist(r_str);
	return ex;
}

double Eval(Tree *tr)
{
	optype op = tr->gtype;
	if (op == DECIMAL)
	{
		return tonumber(tr->value);
	}
    if (op == ENT)
	{
		return atoi(tr->value);
	}
	token sig = tr->tok_type;
	if (op == OPERAT)
	{
		if (sig == ADD)
			return Eval(tr->tleft) + Eval(tr->tright);
		if (sig == SUB)
			return Eval(tr->tleft) - Eval(tr->tright);
		if (sig == PROD)
			return Eval(tr->tleft) * Eval(tr->tright);
		if (sig == DIVID)
			return Eval(tr->tleft) / Eval(tr->tright);
		if (sig == POW)
        {
            if (tr->tleft->gtype == ENT && tr->tright->gtype == ENT)
            {
                return (int)pow(Eval(tr->tleft), Eval(tr->tright));
            }
            return pow(Eval(tr->tleft), Eval(tr->tright));
        }
	}
	else if (op == NEGATION)
		return -Eval(tr->tleft);
	else
	{
		switch (sig)
		{
			case EXP_F:
				return exp(Eval(tr->tleft));
			case LN_F:
				return log(Eval(tr->tleft));
			case SQRT_F:
				return sqrt(Eval(tr->tleft));
			case COS_F:
				return cos(Eval(tr->tleft));
			case ACOS_F:
				return acos(Eval(tr->tleft));
			case SIN_F:
				return sin(Eval(tr->tleft));
			case ASIN_F:
				return asin(Eval(tr->tleft));
			case TAN_F:
				return tan(Eval(tr->tleft));
			case ATAN_F:
				return atan(Eval(tr->tleft));
			case LOG_F:
				return log10(Eval(tr->tleft));
			case LOGBASE_F:
				return (double)log(Eval(tr->tleft->tleft)) / log(Eval(tr->tleft->tright));
			case ABS_F:
				return fabs(Eval(tr->tleft));

			default:
				break;
		}

	}
	return 0;
}

Tree *remplace_tree(Tree *tr, const char* el, Tree *new_el)
{
	Tree *tr_remp = NULL;
	optype op = tr->gtype;
	if (!strcmp(tr->value, el))
		tr_remp = clone(new_el);
	else if (op == ENT || op == DECIMAL || op ==VAR) {
		tr_remp = new_tree(tr->value);
	} else if (op == OPERAT)
		tr_remp = join(remplace_tree(tr->tleft, el, new_el), remplace_tree(tr->tright, el, new_el), tr->value);
	else
		tr_remp = join(remplace_tree(tr->tleft, el, new_el), NULL, tr->value);
	return tr_remp;
}

int tree_compare(Tree *tr1, Tree *tr2)
{
	if (count_tree_nodes(tr1) != count_tree_nodes(tr2))
		return 0;
	token op1 = tr1->tok_type;
	token op2 = tr2->tok_type;
	if (op1 == op2)
	{
		if ((tr1->gtype <= VAR) && !strcmp(tr1->value, tr2->value))
			return 1;
		if (!strcmp(tr1->value, tr2->value))
		{
			if (tr1->gtype == NEGATION || tr1->gtype == FUNCTION)
				return tree_compare(tr1->tleft, tr2->tleft);
			if (op1 == ADD || op1 == PROD)
				return (tree_compare(tr1->tleft, tr2->tleft) && tree_compare(tr1->tright, tr2->tright)) || (tree_compare(tr1->tright, tr2->tleft) && tree_compare(tr1->tleft, tr2->tright));
			return tree_compare(tr1->tleft, tr2->tleft) && tree_compare(tr1->tright, tr2->tright);
		}
	}
	return 0;
}

Tree *clone(Tree *tr)
{
	Tree *tr_cpy = NULL;
	optype op = tr->gtype;
	if (op == OPERAT)
		tr_cpy = join(clone(tr->tleft), clone(tr->tright), tr->value);
	else if (op == NEGATION || op == FUNCTION)
		tr_cpy = join(clone(tr->tleft), NULL, tr->value);
	else
		tr_cpy = new_tree(tr->value);
	return tr_cpy;
}

Tree *substitute(Tree *tr, Tree *av, Tree *ap)
{
	if (tree_compare(tr, av))
		return clone(ap);
	optype g = tr->gtype;
	if (g == OPERAT)
		return join(substitute(tr->tleft, av, ap), substitute(tr->tright, av, ap), tr->value);
	else if (g == NEGATION || g == FUNCTION)
		return join(substitute(tr->tleft, av, ap), NULL, tr->value);
	return clone(tr);
}

int nb_operand(Tree *tr)
{
	optype op = tr->gtype;
	switch (op)
	{
		case (OPERAT):
		case (LOGIC):
			return 2;
		case (NEGATION):
			return 1;
		case (FUNCTION):
			return 1;

		default:
			return 0;
	}
}

Tree *operand(Tree *tr, int i)
{
    if (i == 1)
        return tr->tleft;
    return tr->tright;
}

DList getvars(Tree* tr, DList vrs)
{
	if (tr->tok_type == VARIABLE)
	{
		if (vrs == NULL)
		{
			vrs = push_back_dlist(vrs, tr->value);
			return vrs;
		}
		DListCell* tmp = vrs->begin;
		int k = 0;
		while (tmp != NULL)
		{
			if (!strcmp(tmp->value, tr->value))
			{
				k++;
				break;
			}
			tmp = tmp->next;
		}
		if (!k)
			vrs = push_back_dlist(vrs, tr->value);
		return vrs;
	}
	if (tr->tok_type == NUMBER)
		return vrs;
	if (tr->tleft != NULL)
	{
		vrs = getvars(tr->tleft, vrs);
		if (tr->gtype == OPERAT)
			vrs = getvars(tr->tright, vrs);
	}

	return vrs;
}

string variable(Tree* u)
{
	DList vrs = NULL;
	vrs = getvars(u, vrs);
	if (vrs == NULL)
		return NULL;
	if (vrs->length == 1)
	{
		string vr = malloc((strlen(vrs->begin->value) + 1) * sizeof(string));
		memcpy(vr, vrs->begin->value, strlen(vrs->begin->value) + 1);
		vrs = clear_dlist(vrs);
		return vr;
	}
	DListCell* tmp = vrs->begin;
	int k = 0, w;
	bool t = false;
	string vr = NULL;
	while (tmp != NULL)
	{
		w = found_element(u, tmp->value);
		if (w > k)
		{
			k = w;
			if (t)
				free(vr);
			vr = malloc((strlen(vrs->begin->value) + 1) * sizeof(string));
			memcpy(vr, vrs->begin->value, strlen(vrs->begin->value) + 1);
			t = true;
		}
		tmp = tmp->next;
	}
	vrs = clear_dlist(vrs);
	return vr;
}

#ifdef _EZ80

void print_tree_prefix(Tree* tr)
{
	if (tr == NULL)
		return;

	if (tr->parent != NULL)
		dbg_printf("[%s] -> %s -> type (%d) -> token (%d)\n", tr->parent->value, tr->value, tr->gtype, tr->tok_type);
	else
		dbg_printf("[%s] = type (%d) -> token (%d)\n", tr->value, tr->gtype, tr->tok_type);

	if (tr->tleft != NULL)
		print_tree_prefix(tr->tleft);

	if (tr->tright != NULL)
		print_tree_prefix(tr->tright);
}

#else

void print_tree_prefix(Tree* tr)
{
	if (tr == NULL)
		return;

	if (tr->parent != NULL)
		printf("[%s] -> %s -> type (%d) -> token (%d)\n", tr->parent->value, tr->value, tr->gtype, tr->tok_type);
	else
		printf("[%s] = type (%d) -> token (%d)\n", tr->value, tr->gtype, tr->tok_type);

	if (tr->tleft != NULL)
		print_tree_prefix(tr->tleft);

	if (tr->tright != NULL)
		print_tree_prefix(tr->tright);
}

#endif // _EZ80
