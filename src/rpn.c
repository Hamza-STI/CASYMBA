#include "rpn.h"

/*
https://fr.wikipedia.org/wiki/Table_de_lignes_trigonom%C3%A9triques_exactes
https://fr.wikipedia.org/wiki/Fonction_trigonom%C3%A9trique
http://tibasicdev.wikidot.com/one-byte-tokens
*/

struct Trigo_value Exact_Values[AMONT_VALUE_TRIG] =
{
	/* remarquables */
	{ "0", "1", "0", "0"},
	{ "1/6*PI", "sqrt(3)/2", "1/2", "sqrt(3)/3" },
	{ "1/4*PI", "sqrt(2)/2", "sqrt(2)/2", "1" },
	{ "1/3*PI", "1/2", "sqrt(3)/2", "sqrt(3)" },
	{ "1/2*PI", "1", "0", "undef" },
	{ "2/3*PI", "~1/2", "sqrt(3)/2", "~sqrt(3)"},
	{ "3/4*PI", "~sqrt(2)/2", "sqrt(2)/2", "~1" },
	{ "5/6*PI", "~sqrt(3)/2", "1/2", "~sqrt(3)/3" },
	{ "PI", "~1", "0", "0" },

	/* moins-remarquables */
	{ "1/12*PI", "sqrt(2+sqrt(3))/2", "sqrt(2-sqrt(3))/2", "2-sqrt(3)" },
	{ "1/10*PI", "sqrt(~2*(sqrt(5)-5))/4", "(sqrt(5)-1)/4", "sqrt(1-2*sqrt(5)/5)" },
	{ "1/8*PI", "sqrt(2+sqrt(2))/2", "sqrt(2-sqrt(2))/2", "sqrt(2)-1" },
	{ "1/5*PI", "(sqrt(5)+1)/4", "sqrt(~2*(sqrt(5)-5))/4",	"sqrt(1-2*sqrt(5))" },
	{ "3/8*PI", "sqrt(2-sqrt(2))/2", "sqrt(2+sqrt(2))/2", "sqrt(2)+1" },
	{ "5/12*PI", "sqrt(2-sqrt(3))/2", "sqrt(2+sqrt(3))/2", "2+sqrt(3)" }
};

#define isnumeric(b) ('0' <= b && b <= '9' || b == '.')
#define isvar(b) (('A' <= b && b <= 'Z') || ('a' <= b && b <= 'z'))

DList Parts(DList rpn, int nb)
{
	int i = 1, n = dlist_length(rpn);
	int k = n;
	if (nb == 0)
	{
		string ch = dlist_last(rpn);
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
	string chr = dlist_last(rpn);
	if (!strcmp(chr, "and") || !strcmp(chr, "or"))
		return 2;
	char ch = chr[0];
	if (ch == '+' || ch == '-' || ch == '/' || ch == '*' || ch == '^' || ch == '=' || ch == '>' || ch == '<' || ch == ',')
		return 2;
	else if (isfn(chr) || ch == '~')
		return 1;
	return 0;
}

int prior(const char* s) // priorit� des calculs
{
	char ch = s[0];
	if (isfn(s) || ch == '!')
		return 10;
	else if (ch == '^')
		return 9;
	else if (ch == '~')
		return 8;
	else if (ch == '*' || ch == '/')
		return 7;
	else if (ch == '+' || ch == '-')
		return 6;
	else if (ch == '<' || ch == '=' || ch == '>')
		return 5;
	else if (!strcmp(s, "or"))
		return 4;
	else if (!strcmp(s, "and"))
		return 3;
	else if (ch == ',')
		return 2;
	else if (ch == '(' || ch == ')')
		return 1;
	return 0;
}

int isfn(const char* s)
{
	char fch = s[0], lch = s[strlen(s) - 1];
	if ((('A' <= fch && fch <= 'Z') || ('a' <= fch && fch <= 'z')) && lch == '(' || fch == '!')
		return 1;
	return 0;
}

int cisop(char ch)
{
	return ch == '+' || ch == '-' || ch == '/' || ch == '*' || ch == '^' || ch == '=' || ch == '>' || ch == '<' || ch == '(' || ch == ')' || ch == '~' || ch == ',' || ch == '!';
}

int isop(const char* s)
{
	if (!strcmp(s, "and") || !strcmp(s, "or"))
		return 1;
	return cisop(s[0]);
}

int opless(const char* a, const char* b)
{
	if (a[0] != '~' && a[0] != '^')
		return prior(a) <= prior(b);
	return prior(a) < prior(b);
}

DList In2post(const char* ex)
{
	DList result = NULL;
	char ch, tch;
	char temp[TAILLE_MAX] = { 0 }, op[2] = { 0 };
	int i = 0, sl = 0, p = 0;
	for (i = 0; i < strlen(ex); ++i)
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
			if (sl && (isvar(ch) && isnumeric(temp[sl - 1])) || (isnumeric(ch) && isvar(temp[sl - 1])))
			{
				result = push_back_dlist(result, temp);
				result = push_back_dlist(result, fnc[PROD].ex);
				for (int k = sl - 1; k >= 0; k--)
					temp[k] = '\0';
				sl = 0;
			}
			temp[sl] = ch;
			temp[sl + 1] = '\0';
			sl++;
		}
		else
		{
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
			if (ch == '(')
				p++;
			if (ch == ')')
				p--;
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
	for (i = 0; i < n; ++i)
	{
		if (!(isop(tmp->value) || isfn(tmp->value)))
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
	table_token* element;
	int k = 0;
	for (element = fnc; element != element + AMOUNT_TOKEN; element++)
	{
		if (!strcmp(element->ex, s))
			return element->tok;
		k++;
		if (k == AMOUNT_TOKEN)
			return TOKEN_INVALID;
	}
	return TOKEN_INVALID;
}

Tree* new_tree(const char* x)
{
	Tree* tr = malloc(sizeof(*tr));
	tr->value = malloc(strlen(x) + 1);
	int f = isfn(x);
	int op = isop(x);
	memcpy(tr->value, x, strlen(x) + 1);
	if (f || op)
	{
		tr->parent = NULL;
		if (f)
			tr->gtype = FUNCTION;
		else
		{
			if (x[0] == '~')
				tr->gtype = NEGATION;
			else if (!strcmp(x, "and") || !strcmp(x, "or"))
				tr->gtype = LOGIC;
			else
				tr->gtype = OPERAT;
		}
		tr->tok_type = tokens(x);
	}
	else
	{
		tr->parent = NULL;
		if ('0' <= x[0] && x[0] <= '9')
		{
			string id = strchr(x, '.');
			if (id == NULL)
				tr->gtype = ENT;
			else
				tr->gtype = DECIMAL;
			tr->tok_type = NUMBER;
		}
		else
		{
			tr->gtype = VAR;
			if (!strcmp(x, fnc[UNDEF].ex))
				tr->tok_type = UNDEF;
			else if (!strcmp(x, fnc[IMAGE].ex))
				tr->tok_type = IMAGE;
			else if (!strcmp(x, fnc[PI].ex))
				tr->tok_type = PI;
			else
				tr->tok_type = VARIABLE;
		}
	}
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

int count_tree_nodes(Tree* tr)
{
	if (tr == NULL)
		return 0;

	return (count_tree_nodes(tr->tleft) + count_tree_nodes(tr->tright) + 1);
}

Tree* to_tree(DList list)
{
	string ch = dlist_last(list);
	int n = nparts(list);
	Tree* tr = NULL;
	if (n == 2)
		tr = join(to_tree(Parts(list, 1)), to_tree(Parts(list, 2)), ch);
	else if (n == 1)
		tr = join(to_tree(Parts(list, 1)), NULL, ch);
	else
		tr = new_tree(ch);
	list = clear_dlist(list);
	return tr;
}

int found_element(Tree* tr, const char* elt)
{
	if (tr == NULL || strcmp(tr->value, elt) && tr->tleft == NULL)
		return 0;
	if (!strcmp(tr->value, elt))
		return 1;
	return found_element(tr->tleft, elt) + found_element(tr->tright, elt);
}

double tonumber(const char* ex)
{
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
		snprintf(ex, 50, "%0.9f", t);
	return ex;
}

DList Post2in_rec(Tree* tr, DList rec)
{
	optype op = tr->gtype;
	if (op <= VAR)
	{
		rec = push_back_dlist(rec, tr->value);
		return rec;
	}
	if (op == FUNCTION)
	{
		rec = Post2in_rec(tr->tleft, rec);
		string tmp = malloc((strlen(rec->end->value) + strlen(tr->value) + 1) * sizeof(tmp));
		sprintf(tmp, "%s%s)", tr->value, rec->end->value);
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
		string oper = tr->value;
		if (sig == SUB)
		{
			string tmp = malloc((strlen(pleft) + strlen(pright) + 3) * sizeof(tmp));
			if (tr->tright->tleft != NULL && (tr->tright->tok_type == ADD || tr->tright->tok_type == SUB))
				sprintf(tmp, "%s%s(%s)", pleft, oper, pright);
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
			string tmp1 = malloc((strlen(pleft) + 3) * sizeof(tmp1));
			if (tr->tleft->tleft != NULL && (tr->tleft->tok_type == ADD || tr->tleft->tok_type == SUB))
				sprintf(tmp1, "(%s)%s", pleft, oper);
			else
				sprintf(tmp1, "%s%s", pleft, oper);
			if (tr->tright->tleft != NULL && (tr->tright->tok_type == ADD || tr->tright->tok_type == SUB))
				sprintf(tmp, "%s(%s)", tmp1, pright);
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
			string tmp = malloc((strlen(pleft) + strlen(pright) + 7) * sizeof(tmp));
			string tmp1 = malloc((strlen(pleft) + 3) * sizeof(tmp1));
			if (tr->tleft->tleft != NULL && (tr->tleft->tok_type == ADD || tr->tleft->tok_type == SUB))
				sprintf(tmp1, "(%s)%s", pleft, oper);
			else
				sprintf(tmp1, "%s%s", pleft, oper);
			if (tr->tright->tleft != NULL && (ADD <= tr->tright->tok_type && tr->tright->tok_type <= POW))
				sprintf(tmp, "%s(%s)", tmp1, pright);
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
				sprintf(tmp1, "(%s)%s", pleft, oper);
			else
				sprintf(tmp1, "%s%s", pleft, oper);
			if (tr->tright->tleft != NULL && ((ADD <= tr->tright->tok_type && tr->tright->tok_type <= POW) || tr->tright->tok_type == NEGATIF))
				sprintf(tmp, "%s(%s)", tmp1, pright);
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
			if (sig == ADD && pright[0] == '~')
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
		rec = Post2in_rec(tr->tleft, rec);
		rec = Post2in_rec(tr->tright, rec);
		string pleft = rec->end->back->value;
		string pright = rec->end->value;
		string tmp = malloc((strlen(pleft) + strlen(pright) + strlen(tr->value) + 2)*sizeof(tmp));
		sprintf(tmp, "%s %s %s", pleft, tr->value, pright);
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
				string tmp = malloc((strlen(rec->end->value) + 3)*sizeof(tmp));
				sprintf(tmp, "~(%s)", rec->end->value);
				rec = pop_back_dlist(rec);
				rec = push_back_dlist(rec, tmp);
				free(tmp);
				return rec;
			}
		}
		string tmp = malloc((strlen(rec->end->value) + 1)*sizeof(tmp));
		sprintf(tmp, "~%s", rec->end->value);
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
	r_str = clear_dlist(r_str);
	return ex;
}

double Eval(Tree* tr)
{
	optype op = tr->gtype;
	if (op == ENT || op == DECIMAL)
	{
		return tonumber(tr->value);
	}
	string sig = tr->value;
	if (op == OPERAT)
	{
		if (sig[0] == '+')
			return Eval(tr->tleft) + Eval(tr->tright);
		if (sig[0] == '-')
			return Eval(tr->tleft) - Eval(tr->tright);
		if (sig[0] == '*')
			return Eval(tr->tleft) * Eval(tr->tright);
		if (sig[0] == '/')
			return Eval(tr->tleft) / Eval(tr->tright);
		if (sig[0] == '^')
			return pow(Eval(tr->tleft), Eval(tr->tright));
	}
	else if (op == NEGATION)
		return -Eval(tr->tleft);
	else
	{
		if (!strcmp(sig, "exp("))
			return exp(Eval(tr->tleft));
		if (!strcmp(sig, "ln("))
			return log(Eval(tr->tleft));
		if (!strcmp(sig, "sqrt("))
			return sqrt(Eval(tr->tleft));
		if (!strcmp(sig, "cos("))
			return cos(Eval(tr->tleft));
		if (!strcmp(sig, "acos("))
			return acos(Eval(tr->tleft));
		if (!strcmp(sig, "sin("))
			return sin(Eval(tr->tleft));
		if (!strcmp(sig, "asin("))
			return asin(Eval(tr->tleft));
		if (!strcmp(sig, "tan("))
			return tan(Eval(tr->tleft));
		if (!strcmp(sig, "atan("))
			return atan(Eval(tr->tleft));
		if (!strcmp(sig, "floor("))
			return floor(Eval(tr->tleft));
		if (!strcmp(sig, "ceil("))
			return ceil(Eval(tr->tleft));
		if (!strcmp(sig, "log10("))
			return log10(Eval(tr->tleft));
		if (!strcmp(sig, "logb("))
			return log(Eval(tr->tleft->tleft)) / log(Eval(tr->tleft->tright));
		if (!strcmp(sig, "abs("))
			return fabs(Eval(tr->tleft));
		if (!strcmp(sig, "sign("))
		{
			double a = Eval(tr->tleft);
			return (a == 0) ? 0 : a / fabs(a);
		}
	}
	return 0;
}

Tree* remplace_tree(Tree* tr, const char* v, Tree* u)
{
	optype op = tr->gtype;
	if (!strcmp(tr->value, v))
	{
		Tree* q = clone(u);
		q->parent = tr->parent;
		clean_tree(tr);
		return q;
	}
	else if (op == ENT || op == DECIMAL || op == VAR)
		return tr;
	else if (op == OPERAT)
	{
		tr->tleft = remplace_tree(tr->tleft, v, u);
		tr->tright = remplace_tree(tr->tright, v, u);
		return tr;
	}
	tr->tleft = remplace_tree(tr->tleft, v, u);
	return tr;
}

int tree_compare(Tree* tr1, Tree* tr2)
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

Tree* clone(Tree* tr)
{
	Tree* tr_cpy = NULL;
	optype op = tr->gtype;
	if (op == OPERAT)
		tr_cpy = join(clone(tr->tleft), clone(tr->tright), tr->value);
	else if (op == NEGATION || op == FUNCTION)
		tr_cpy = join(clone(tr->tleft), NULL, tr->value);
	else
		tr_cpy = new_tree(tr->value);
	return tr_cpy;
}

Tree* substitute(Tree* tr, Tree* av, Tree* ap)
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

int nb_operand(Tree* tr)
{
	optype op = tr->gtype;
	switch (op)
	{
	case (OPERAT):
		return 2;
	case (NEGATION):
		return 1;
	case (FUNCTION):
		return 1;

	default:
		return 0;
	}
}

Tree* operand(Tree* tr, int i)
{
	if (i == 1)
		return tr->tleft;
	return tr->tright;
}

DList getvars(Tree* tr, DList vrs)
{
	if (tr->gtype == VAR)
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
			vr = malloc((strlen(tmp->value) + 1) * sizeof(string));
			memcpy(vr, tmp->value, strlen(tmp->value) + 1);
			t = true;
		}
		tmp = tmp->next;
	}
	vrs = clear_dlist(vrs);
	return vr;
}

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
