#include "includes.h"

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
	{{0xB2}, 1}, {{'S', 'I', 'G', 'N', 0x10}, 5}, {{0xC4}, 1}, {{0xC2}, 1}, {{0xC6}, 1}, {{0xC5}, 1},
	{{0xC3}, 1}, {{0xC7}, 1}, {{0xCA}, 1}, { {0xC8}, 1}, {{0xCC}, 1}, {{0xCB}, 1}, {{0xC9}, 1},
	{{0xCD}, 1}, {{0x2D}, 1}, {{0xF1}, 1},
	/*COMPLEX FUNCTIONS */
	{{0xBB, 0x25}/*conj(*/, 2}, {{0xBB, 0x26}/*real(*/, 2}, {{0xBB, 0x27}/*image(*/, 2}, {{0xBB, 0x28}/*angle(*/, 2},
	/* ANALYSE FUNCTIONS */
	{{0x25}, 1}, {{0x24}, 1}, {{0x22} /*solve(*/, 1}, {{0xA7}, 1}, {{0xEF, 0x32}, 2},
	{{0xB1}, 1}, {{0xBB, 0x09}, 2}, {{0xBB, 0x2A}/*expr(*/, 2}, {{0xBB, 0x0D}/*stdDev(*/, 2}, {{0xB4}/*identity(*/, 1}, {{0xB3}/*det(*/, 1}
};

struct table_token fnc[AMOUNT_TOKEN] =
{
	{ "\0", 0}, { "\0", 0}, { "UNDEF", 5}, { "@i", 2}, { "PI", 2}, { "^(~1)", 5}, { "^2", 2}, { "^3", 2},
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
	{ "abs(", 4}, { "sign(", 5}, { "cos(", 4}, { "sin(", 4}, { "tan(", 4},  { "acos(", 5}, { "asin(", 5},
	{ "atan(", 5}, { "cosh(", 6}, { "sinh(", 6}, { "tanh(", 6}, { "acosh(", 7}, { "asinh(", 7}, { "atanh(", 7},
	{ "!", 1}, { "root(", 5},
	/* COMPLEX FUNCTION */
	{ "conj(", 5}, { "real(", 5}, { "image(", 6}, { "angle(", 6},
	/* ANALYSE FUNCTIONS */
	{ "diff(", 5}, { "integral(", 9}, { "desolve(", 8}, { "tangent(", 8}, { "polyrem(", 8},
	{ "polyquot(", 9}, {"polygcd(", 8}, {"polysimp(", 9}, { "expand(", 7}, {"factor(", 7}, { "taylor(", 7}
};

bool is_negation(Tree* u)
{
	if (u->tok_type == NEGATIF)
		return !is_negation(u->tleft);
	if (u->tok_type == PROD || u->tok_type == DIVID)
		return is_negation(u->tleft) || is_negation(u->tright);
	return false;
}

bool isconstant(Tree* tr)
{
	optype op = tr->gtype;
	if (op == ENT || op == DECIMAL)
		return true;
	if (tr->tok_type == FACTORIEL_F || op == NEGATION || tr->tok_type == ABS_F)
		return isconstant(tr->tleft);
	if (op == VAR || op == FUNCTION)
		return false;
	if (tr->tok_type == POW)
	{
		if (is_negation(tr->tleft) && tr->tright->gtype != ENT)
			return false;
		if (tr->tright->gtype <= ENT || (tr->tright->tok_type == NEGATIF && tr->tright->tleft->gtype == ENT))
			return isconstant(tr->tleft);
		return false;
	}
	return isconstant(tr->tleft) && isconstant(tr->tright);
}

bool is_symbolic(Tree* tr)
{
	optype op = tr->gtype;
	if (op == VAR)
		return false;
	if (op <= VAR)
		return true;
	if (op < OPERAT)
		return is_symbolic(tr->tleft);
	return is_symbolic(tr->tleft) && is_symbolic(tr->tright);
}

bool isfn(const char* s)
{
	return ((IS_VAR((uint8_t)s[0]) && s[strlen(s) - 1] == '(') || s[0] == '!');
}

static int nparts(List rpn)
{
	token tk = tokens(rpn->end->data, fnc);
	if (ADD <= tk && tk <= LOGIC_OR)
		return 2;
	return (NEGATIF <= tk && tk < AMOUNT_TOKEN) || isfn(rpn->end->data);
}

static List Parts(List rpn, int nb)
{
	int i = 1, n = rpn->length;
	int k = n;
	while (i > 0)
	{
		k--;
		List lf = dlist_left(rpn, k);
		i = i + nparts(lf) - 1;
		lf = clear_dlist(lf);
	}
	if (nb == 1 && k > 1)
		return dlist_left(rpn, k - 1);
	return dlist_sub(rpn, k, n - k);
}

static int prior(const char* s)
{
	token ch = tokens(s, fnc);
	if ((NEGATIF < ch && ch < AMOUNT_TOKEN) || isfn(s))
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
	return (ch == PAR_FERMANT || ch == PAR_OUVRANT);
}

static bool cisop(char ch)
{
	return strchr("+-/*^=><()~,!", ch) != NULL && ch != '\0';
}

static bool isop(const char* s)
{
	if (!strcmp(s, "and") || !strcmp(s, "or"))
		return true;
	return cisop(s[0]);
}

static bool opless(const char* a, const char* b)
{
	if (a[0] != '~' && a[0] != '^')
		return prior(a) <= prior(b);
	return prior(a) < prior(b);
}

static List parse(const uint8_t* ex, unsigned k, bool ce_parse)
{
	List result = NULL;
	char temp[TAILLE_MAX] = { 0 }, chr[3] = { 0 };
	int sl, p = 0;
	temp[0] = '\0';
	for (unsigned i = 0; i < k; ++i)
	{
		uint8_t ch = ex[i];
		chr[0] = ch;
		chr[1] = '\0';
		token tk = tokens(chr, (ce_parse) ? ti_table : fnc);
		sl = strlen(temp);
		if (ch == ' ')
		{
			if (sl)
				result = push_back_dlist(result, temp);
			memset(temp, 0, sl * sizeof(char));
		}
		else if (UNDEF < tk && tk <= PI)
		{
			if (result == NULL)
				result = push_back_dlist(result, fnc[tk].ex);
			else
			{
				if (sl > 0)
				{
					result = push_back_dlist(push_back_dlist(result, temp), fnc[PROD].ex);
					memset(temp, 0, sl * sizeof(char));
				}
				else if (result != NULL)
				{
					token t = tokens(result->end->data, fnc);
					if (!(ADD <= t && t <= NEGATIF) && t != PAR_OUVRANT && t != TOKEN_INVALID)
						result = push_back_dlist(result, fnc[PROD].ex);
				}
				result = push_back_dlist(result, fnc[tk].ex);
			}
		}
		else if (ch == 0xBB || ch == 0xEF)
		{
			i++;
			char fn[3] = { ch, ex[i] };
			token tk = tokens(fn, ti_table);
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
					token t = tokens(result->end->data, fnc);
					if (!(ADD <= t && t <= NEGATIF) && t != PAR_OUVRANT && t != TOKEN_INVALID)
						result = push_back_dlist(result, fnc[PROD].ex);
				}
				result = push_back_dlist(result, fnc[tk].ex);
				if (EXP_F <= tk && tk < AMOUNT_TOKEN)
				{
					result = push_back_dlist(result, fnc[PAR_OUVRANT].ex);
					p++;
				}
				memset(temp, 0, sl * sizeof(char));
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
				result = push_back_dlist(push_back_dlist(push_back_dlist(push_back_dlist(result, fnc[PAR_OUVRANT].ex), fnc[NEGATIF].ex), "1"), fnc[PAR_FERMANT].ex);
			else if (tk == CARRE)
				result = push_back_dlist(result, "2");
			else
				result = push_back_dlist(result, "3");
			memset(temp, 0, sl * sizeof(char));
		}
		else if (tk == TOK_10_POWER)
		{
			if (sl)
				result = push_back_dlist(push_back_dlist(result, temp), fnc[PROD].ex);
			result = push_back_dlist(push_back_dlist(push_back_dlist(result, "10"), fnc[POW].ex), fnc[PAR_OUVRANT].ex);
			memset(temp, 0, sl * sizeof(char));
		}
		else if (tk == ROOT_F)
		{
			uint8_t root_chars[TAILLE_MAX] = { 0 };
			int par = 0, pos = 0;
			++i;
			while (par >= 0)
			{
				if (ex[i] == 0x10)
					++par;
				if (ex[i] == 0x11)
					--par;
				if (par >= 0)
				{
					root_chars[pos] = (uint8_t)ex[i];
					++pos;
				}
				++i;
			}
			--i;
			List rtl = parse(root_chars, pos, ce_parse);
			result = push_back_dlist(push_back_dlist(result, fnc[tk].ex), fnc[PAR_OUVRANT].ex);
			for (Cell* tmp = rtl->begin; tmp != NULL; tmp = tmp->next)
				result = push_back_dlist(result, (char*)tmp->data);
			rtl = clear_dlist(rtl);
			result = push_back_dlist(push_back_dlist(push_back_dlist(result, fnc[SEPARATEUR].ex), (sl) ? temp : "2"), fnc[PAR_FERMANT].ex);
			memset(temp, 0, sl * sizeof(char));
		}
		else if (tk == TOKEN_INVALID && !isop(chr))
		{
			if (!IS_VAR(ch) && !IS_NUMERIC(ch))
			{
				if (result != NULL)
					result = clear_dlist(result);
				return NULL;
			}
			if (strlen(temp) == 0)
			{
				if (result != NULL && ex[i - 1] != ' ')
				{
					token t = tokens(result->end->data, fnc);
					if (t == PAR_FERMANT || t == PI || t == IMAGE || t == FACTORIEL_F)
						result = push_back_dlist(result, fnc[PROD].ex);
				}
				temp[sl] = ch;
				temp[sl + 1] = '\0';
			}
			else
			{
				if ((IS_VAR((uint8_t)temp[0]) && IS_NUMERIC(ch)) || (IS_VAR(ch) && IS_NUMERIC(temp[0])))
				{
					result = push_back_dlist(push_back_dlist(result, temp), fnc[PROD].ex);
					memset(temp, 0, sl * sizeof(char));
					sl = 0;
				}
				if (ch == 0x3A)
					ch = '.';
				if (ch == 0xAE)
					ch = '\'';
				temp[sl] = ch;
				temp[sl + 1] = '\0';
				if (!strcmp(temp, fnc[PI].ex) || !strcmp(temp, fnc[IMAGE].ex))
				{
					result = push_back_dlist(result, temp);
					memset(temp, 0, sl * sizeof(char));
				}
				else if (!strcmp(temp, "pi"))
				{
					result = push_back_dlist(result, fnc[PI].ex);
					memset(temp, 0, sl * sizeof(char));
				}
			}
		}
		else
		{
			if (tk == PAR_OUVRANT || (EXP_F <= tk && tk < AMOUNT_TOKEN && tk != FACTORIEL_F && tk != ROOT_F))
				p++;
			if (tk == PAR_FERMANT)
				p--;
			if (sl != 0)
			{
				if (tk == PAR_OUVRANT && IS_VAR((uint8_t)temp[0]) && !ce_parse)
				{
					temp[sl] = ch;
					temp[sl + 1] = '\0';
					result = push_back_dlist(result, temp);
				}
				else
				{
					result = push_back_dlist(result, temp);
					if (((EXP_F <= tk && tk < AMOUNT_TOKEN) || tk == PAR_OUVRANT) && tk != FACTORIEL_F)
						result = push_back_dlist(result, fnc[PROD].ex);
				}
			}
			else if (result != NULL && tk != PAR_FERMANT && !(ADD <= tk && tk <= LOGIC_OR) && tokens(result->end->data, fnc) == PAR_FERMANT)
				result = push_back_dlist(result, fnc[PROD].ex);
			if (tk == SUB)
			{
				if (result == NULL)
					tk = NEGATIF;
				else
				{
					token t = tokens(result->end->data, fnc);
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
				token t = tokens(result->end->data, fnc);
				if (((ADD <= t && t <= LOGIC_OR) && tk == PAR_FERMANT) ||
					(((ADD <= t && t <= LOGIC_OR) || t == NEGATIF || t == PAR_OUVRANT) && (ADD <= tk && tk <= LOGIC_OR)))
				{
					result = clear_dlist(result);
					return NULL;
				}
			}
			result = push_back_dlist(result, fnc[tk].ex);
			if ((EXP_F <= tk && tk < AMOUNT_TOKEN) && tk != FACTORIEL_F && tk != ROOT_F)
				result = push_back_dlist(result, fnc[PAR_OUVRANT].ex);
			memset(temp, 0, sl * sizeof(char));
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
	return result;
}

static List to_rpn(List* result)
{
	int stklen = 0;
	List rlt = NULL, opstack = NULL;
	for (Cell* tmp = (*result)->begin; tmp != NULL; tmp = tmp->next)
	{
		if (!isop((char*)tmp->data) && !isfn((char*)tmp->data))
			rlt = push_back_dlist(rlt, (char*)tmp->data);
		else
		{
			if (((char*)tmp->data)[0] != '(' && ((char*)tmp->data)[0] != ')')
			{
				while (opstack != NULL && opless((char*)tmp->data, opstack->end->data) && stklen > 0)
				{
					rlt = push_back_dlist(rlt, opstack->end->data);
					opstack = pop_back_dlist(opstack);
					stklen--;
				}
			}
			if (((char*)tmp->data)[0] == ')')
			{
				while (opstack != NULL && ((char*)opstack->end->data)[0] != '(' && stklen > 0)
				{
					rlt = push_back_dlist(rlt, (char*)opstack->end->data);
					opstack = pop_back_dlist(opstack);
					stklen--;
				}
				opstack = pop_back_dlist(opstack);
				stklen--;
			}
			if (((char*)tmp->data)[0] != ')')
			{
				opstack = push_back_dlist(opstack, (char*)tmp->data);
				stklen++;
			}
		}
	}
	while (opstack != NULL)
	{
		rlt = push_back_dlist(rlt, opstack->end->data);
		opstack = pop_back_dlist(opstack);
	}
	*result = clear_dlist(*result);
	opstack = clear_dlist(opstack);
	return rlt;
}

List In2post(const uint8_t* ex, unsigned k)
{
	List result = parse(ex, k, true);
	if (result == NULL)
		return result;
	return to_rpn(&result);
}

List In2post2(const char* ex)
{
	List result = parse((uint8_t*)ex, strlen(ex), false);
	if (result == NULL)
		return result;
	return to_rpn(&result);
}

int tokens(const char* s, struct table_token* w)
{
	int k = 0;
	for (table_token* element = w; element != w + AMOUNT_TOKEN; element++)
	{
		if (!strcmp(element->ex, s))
			return k;
		++k;
	}
	return TOKEN_INVALID;
}

Tree* new_tree(const char* x)
{
	Tree* tr = malloc(sizeof(Tree));
	tr->value = strdup(x);
	token tk = tokens(x, fnc);
	if (tk != TOKEN_INVALID || isfn(x))
	{
		tr->parent = NULL;
		if ((EXP_F <= tk && tk < AMOUNT_TOKEN) || isfn(x))
			tr->gtype = FUNCTION;
		else if (tk == NEGATIF)
			tr->gtype = NEGATION;
		else if (tk == LOGIC_AND || tk == LOGIC_OR)
			tr->gtype = LOGIC;
		else if (ADD <= tk && tk <= SUPERIEUR_EGAL)
			tr->gtype = OPERAT;
		else if (UNDEF <= tk && tk <= PI)
			tr->gtype = VAR;
		tr->tok_type = tk;
	}
	else if (IS_NUMERIC(x[0]))
	{
		tr->gtype = (strchr(tr->value, '.') == NULL) ? ENT : DECIMAL;
		tr->tok_type = NUMBER;
	}
	else
	{
		tr->tok_type = VARIABLE;
		tr->gtype = VAR;
	}
	tr->parent = NULL;
	tr->tleft = NULL;
	tr->tright = NULL;
	return tr;
}

void clean_tree(Tree* tr)
{
	if (tr == NULL)
		return;

	clean_tree(tr->tleft);
	clean_tree(tr->tright);
	free(tr->value);
	free(tr);
}

void clean_noeud(Tree* tr)
{
	if (tr == NULL)
		return;
	free(tr->value);
	free(tr);
}

Tree* join(Tree* left, Tree* right, const char* node)
{
	Tree* tr = new_tree(node);

	tr->tleft = left;
	tr->tright = right;

	if (left != NULL)
		left->parent = tr;
	if (right != NULL)
		right->parent = tr;

	return tr;
}

int count_tree_nodes(Tree* tr)
{
	if (tr == NULL)
		return 0;

	return (count_tree_nodes(tr->tleft) + count_tree_nodes(tr->tright) + 1);
}

Tree* to_tree(List list)
{
	string ch = list->end->data;
	int n = nparts(list);
	Tree* tr = NULL;
	if (n > 0)
		tr = join(to_tree(Parts(list, 1)), (n == 2) ? to_tree(Parts(list, 2)) : NULL, ch);
	else
		tr = new_tree(ch);
	clear_dlist(list);
	return tr;
}

int found_element(Tree* tr, const char* elt)
{
	if (tr == NULL || (strcmp(tr->value, elt) && tr->tleft == NULL))
		return 0;
	if (!strcmp(tr->value, elt))
		return 1;
	return found_element(tr->tleft, elt) + found_element(tr->tright, elt);
}

double tonumber(const char* ex)
{
	char* t = strchr(ex, '.');
	if (t != NULL)
		return strtod(ex, NULL);
	return strtoul(ex, NULL, 10);
}

string tostr(double t)
{
	static char ex[50];
	snprintf(ex, 50, "%0.9f", t);
	int k = strlen(ex) - 1;
	while (ex[k] == '0')
	{
		ex[k] = '\0';
		k--;
	}
	if (ex[k] == '.') ex[k] = '\0';
	return ex;
}

static string post2in_common(const char* pleft, const char* pright, const char* oper, bool a, bool b, struct table_token* tb)
{
	string tmp = malloc((strlen(pleft) + strlen(pright) + 7) * sizeof(tmp));
    string tmp1 = malloc((strlen(pleft) + 3) * sizeof(tmp1));
    if (a)
        sprintf(tmp1, "%s%s%s%s", tb[PAR_OUVRANT].ex, pleft, tb[PAR_FERMANT].ex, oper);
    else
        sprintf(tmp1, "%s%s", pleft, oper);
    if (b)
        sprintf(tmp, "%s%s%s%s", tmp1, tb[PAR_OUVRANT].ex, pright, tb[PAR_FERMANT].ex);
    else
        sprintf(tmp, "%s%s", tmp1, pright);
    free(tmp1);
    return tmp;
}

static List Post2in_rec(Tree* tr, List rec, struct table_token* tb)
{
	optype op = tr->gtype;
	if (op <= VAR)
	{
		if (tr->tok_type == PI || tr->tok_type == IMAGE)
			rec = push_back_dlist(rec, tb[tr->tok_type].ex);
		else
		{
			if (op == DECIMAL && tb[EXP_F].length == ti_table[EXP_F].length)
			{
				size_t t = strlen(tr->value);
				for (unsigned int i = 0; i < t; ++i)
					if (tr->value[i] == '.')
						tr->value[i] = 0x3A;
			}
			rec = push_back_dlist(rec, tr->value);
		}
		return rec;
	}
	if (op == FUNCTION)
	{
		rec = Post2in_rec(tr->tleft, rec, tb);
		if (tr->tok_type == FACTORIEL_F)
		{
			string tmp = malloc((strlen((char*)rec->end->data) + 3) * sizeof(tmp));
			if (tr->tleft->gtype == OPERAT)
				sprintf(tmp, "%s%s%s%s", tb[PAR_OUVRANT].ex, (char*)rec->end->data, tb[PAR_FERMANT].ex, tb[tr->tok_type].ex);
			else
				sprintf(tmp, "%s%s", (char*)rec->end->data, tb[tr->tok_type].ex);
			rec = push_back(pop_back_dlist(rec), tmp);
			return rec;
		}
		string tmp = malloc((strlen((char*)rec->end->data) + tb[tr->tok_type].length + 1) * sizeof(tmp));
		sprintf(tmp, "%s%s%s", tb[tr->tok_type].ex, (char*)rec->end->data, tb[PAR_FERMANT].ex);
		rec = push_back(pop_back_dlist(rec), tmp);
		return rec;
	}
	else if (op == OPERAT || op == LOGIC)
	{
		token sig = tr->tok_type;
		rec = Post2in_rec(tr->tright, Post2in_rec(tr->tleft, rec, tb), tb);
		string pleft = rec->end->back->data, pright = (char*)rec->end->data, oper = tb[(sig == DIVID)? FRACTION : sig].ex;
		if (ADD < sig && sig <= POW)
		{
			bool cond1 = false, cond2 = false;
			if (sig == SUB)
				cond2 = tr->tright->tleft != NULL && (tr->tright->tok_type == ADD || tr->tright->tok_type == SUB);
			else if (sig == PROD)
			{
				if (!strcmp(pleft, "1"))
					return dlist_remove_id(rec, rec->length - 1);
				if (!strcmp(pright, "1"))
					return pop_back_dlist(rec);
				cond1 = tr->tleft->tleft != NULL && (tr->tleft->tok_type == ADD || tr->tleft->tok_type == SUB);
				cond2 = tr->tright->tleft != NULL && (tr->tright->tok_type == ADD || tr->tright->tok_type == SUB);
			}
			else
			{
				if (!strcmp(pright, "1"))
					return pop_back_dlist(rec);
				if (sig == DIVID)
				{
					cond1 = tr->tleft->tleft != NULL && (ADD <= tr->tleft->tok_type && tr->tleft->tok_type <= PROD);
					cond2 = tr->tright->tleft != NULL && (ADD <= tr->tright->tok_type && tr->tright->tok_type <= POW);
				}
				else if (sig == POW)
				{
					cond1 = tr->tleft->tleft != NULL && ((ADD <= tr->tleft->tok_type && tr->tleft->tok_type <= POW) || tr->tleft->tok_type == NEGATIF);
					cond2 = tr->tright->tleft != NULL && ((ADD <= tr->tright->tok_type && tr->tright->tok_type <= POW) || tr->tright->tok_type == NEGATIF);
				}
			}
			string tmp = post2in_common(pleft, pright, oper, cond1, cond2, tb);
			rec = push_back(pop_back_dlist(pop_back_dlist(rec)), tmp);
			return rec;
		}
		else
		{
			string tmp = malloc((strlen(pleft) + strlen(pright) + 1) * sizeof(tmp));
			if (sig == ADD && (pright[0] == (char)0xB0 || pright[0] == '~'))
			{
				pright[0] = tb[SUB].ex[0];
				sprintf(tmp, "%s%s", pleft, pright);
			}
			else if (op == LOGIC && tb[EXP_F].length != ti_table[EXP_F].length)
				sprintf(tmp, "%s %s %s", pleft, oper, pright);
			else
				sprintf(tmp, "%s%s%s", pleft, oper, pright);
			rec = push_back_dlist(pop_back_dlist(pop_back_dlist(rec)), tmp);
			free(tmp);
			return rec;
		}
	}
	else
	{
		rec = Post2in_rec(tr->tleft, rec, tb);
		if (tr->tleft->tleft != NULL)
		{
			token sigt = tr->tleft->tok_type;
			if (sigt == ADD || sigt == SUB)
			{
				string tmp = malloc((strlen((char*)rec->end->data) + 3) * sizeof(tmp));
				sprintf(tmp, "%s%s%s%s", tb[NEGATIF].ex, tb[PAR_OUVRANT].ex, (char*)rec->end->data, tb[PAR_FERMANT].ex);
				rec = push_back_dlist(pop_back_dlist(rec), tmp);
				free(tmp);
				return rec;
			}
		}
		string tmp = malloc((strlen((char*)rec->end->data) + 1) * sizeof(tmp));
		sprintf(tmp, "%s%s", tb[NEGATIF].ex, (char*)rec->end->data);
		rec = push_back_dlist(pop_back_dlist(rec), tmp);
		free(tmp);
		return rec;
	}
}

string Post2in(Tree* tr, struct table_token* tb)
{
	List rec = NULL;
	List r_str = Post2in_rec(tr, rec, tb);
	string ex = strdup(r_str->begin->data);
	r_str = clear_dlist(r_str);
	return ex;
}

double Eval(Tree* tr)
{
	optype op = tr->gtype;
	if (op < VAR)
		return tonumber(tr->value);
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
			return pow(Eval(tr->tleft), Eval(tr->tright));
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

Tree* remplace_tree(Tree* tr, const char* el, Tree* new_el)
{
    Tree* av = new_tree(el);
	Tree* rp = substitute(tr, av, new_el);
    clean_tree(av);
	return rp;
}

Tree* remplace_var(Tree* u, const char* v, Tree* w)
{
	Tree* y = remplace_tree(u, v, w);
	clean_tree(u);
	return y;
}

bool tree_compare(Tree* tr1, Tree* tr2)
{
	if (count_tree_nodes(tr1) != count_tree_nodes(tr2))
		return false;
	token op1 = tr1->tok_type, op2 = tr2->tok_type;
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
	return false;
}

Tree* clone(Tree* tr)
{
	optype op = tr->gtype;
	if (op == OPERAT || op == LOGIC)
		return join(clone(tr->tleft), clone(tr->tright), tr->value);
	else if (op == NEGATION || op == FUNCTION)
		return join(clone(tr->tleft), NULL, tr->value);
	return new_tree(tr->value);
}

Tree* substitute(Tree* tr, Tree* av, Tree* ap)
{
	if (tree_compare(tr, av))
		return clone(ap);
	optype g = tr->gtype;
	if (g >= OPERAT)
		return join(substitute(tr->tleft, av, ap), substitute(tr->tright, av, ap), tr->value);
	else if (g == NEGATION || g == FUNCTION)
		return join(substitute(tr->tleft, av, ap), NULL, tr->value);
	return clone(tr);
}

int nb_operand(Tree* tr)
{
	optype op = tr->gtype;
	if (op >= OPERAT)
		return 2;
	return (op == NEGATION || op == FUNCTION);
}

Tree* operand(Tree* tr, int i)
{
	return (i == 1) ? tr->tleft : tr->tright;
}

List getvars(Tree* tr, List vrs)
{
	if (tr->tok_type == VARIABLE)
	{
		if (vrs == NULL)
			return push_back_dlist(vrs, tr->value);
		for (Cell* tmp = vrs->begin; tmp != NULL; tmp = tmp->next)
			if (!strcmp((char*)tmp->data, tr->value))
				return vrs;
		return push_back_dlist(vrs, tr->value);
	}
	if (tr->tok_type == NUMBER)
		return vrs;
	if (tr->tleft != NULL)
	{
		vrs = getvars(tr->tleft, vrs);
		if (tr->tright != NULL)
			vrs = getvars(tr->tright, vrs);
	}
	return vrs;
}

string variable(Tree* u)
{
	List vrs = NULL;
	vrs = getvars(u, vrs);
	if (vrs == NULL)
		return NULL;
	if (vrs->length == 1)
	{
		string vr = strdup(vrs->begin->data);
		vrs = clear_dlist(vrs);
		return vr;
	}
	int k = 0, w;
	bool t = false;
	string vr = NULL;
	for (Cell* tmp = vrs->begin; tmp != NULL; tmp = tmp->next)
	{
		w = found_element(u, (char*)tmp->data);
		if (w > k)
		{
			k = w;
			if (t)
				free(vr);
			vr = strdup((char*)tmp->data);
			t = true;
		}
	}
	vrs = clear_dlist(vrs);
	return vr;
}
