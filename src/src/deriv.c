#include "includes.h"

static Tree* form_integral(const char* s_form, struct Integral* w, int size)
{
	for (const Integral* element = w; element != w + size; element++)
		if (!strcmp(element->from, s_form))
			return to_tree(In2post2(element->to));
	return NULL;
}

struct Integral Derivtable[] =
{
	{ fnc[LN_F].ex, "V/U", "" },
	{ fnc[LOG_F].ex, "V/(U*ln(10))", "" },
	{ fnc[EXP_F].ex, "V*exp(U)", "" },
	{ fnc[ABS_F].ex, "V*sign(U)", "" },
	{ fnc[SQRT_F].ex, "V/(2*sqrt(U))", "" },
	{ fnc[COS_F].ex, "~V*sin(U)", "" },
	{ fnc[SIN_F].ex, "V*cos(U)", "" },
	{ fnc[TAN_F].ex, "V/cos(U)^2", "" },
	{ fnc[COSH_F].ex, "V*sinh(U)", "" },
	{ fnc[SINH_F].ex, "V*cosh(U)", "" },
	{ fnc[TANH_F].ex, "V/cosh(U)^2", "" },
	{ fnc[ACOS_F].ex, "~V/sqrt(1-U^2)", "" },
	{ fnc[ASIN_F].ex, "V/sqrt(1-U^2)", "" },
	{ fnc[ATAN_F].ex, "V/(U^2+1)", "" },
	{ fnc[ACOSH_F].ex, "V/sqrt(U^2-1)", "" },
	{ fnc[ASINH_F].ex, "V/sqrt(1+U^2)", "" },
	{ fnc[ATANH_F].ex, "V/(1-U^2)", "" },
	{ fnc[CBRT_F].ex, "V/(3*U^(2/3))", "" }
};

Tree* diff(Tree* tr, const char* vr)
{
	if (!found_element(tr, vr))
		return new_tree("0");
	if (!strcmp(tr->value, vr))
		return new_tree("1");
	string sig = tr->value;
	token tok = tr->tok_type;
	if (tr->gtype == OPERAT)
	{
		Tree* dl = diff(tr->tleft, vr), * dr = diff(tr->tright, vr);
		if (tok == ADD || tok == SUB)
			return simplify(join(dl, dr, sig));
		if (tok == PROD || tok == DIVID)
		{
			Tree* t = simplify(join(join(dl, clone(tr->tright), fnc[PROD].ex), join(dr, clone(tr->tleft), fnc[PROD].ex), fnc[(tok == PROD) ? ADD : SUB].ex));
			return (tok == PROD) ? t : join(t, join(clone(tr->tright), new_tree("2"), fnc[POW].ex), fnc[DIVID].ex);
		}
		if (tok == POW)
		{
			Tree* sol = NULL;
			bool v = !strcmp(dr->value, "0");
			if (v || !strcmp(dl->value, "0"))
			{
				sol = to_tree(In2post2(v ? "C*V*U^(C-1)" : "V*ln(C)*C^U"));
				sol = remplace_var(remplace_var(remplace_var(sol, "U", v ? tr->tleft : tr->tright), "V", v ? dl : dr), "C", v ? tr->tright : tr->tleft);
			}
			else
				sol = remplace_var(remplace_var(remplace_var(remplace_var(to_tree(In2post2("(T*V/U+ln(U)*W)*U^V")), "U", tr->tleft), "V", tr->tright), "T", dl), "W", dr);
			clean_tree(dr); clean_tree(dl);
			return sol;
		}
	}
	else if (tok == NEGATIF)
		return join(simplify(diff(tr->tleft, vr)), NULL, sig);
	if (tok == INTEGRAL_F)
	{
		Tree* t = tr;
		while (t->tleft->tok_type == SEPARATEUR)
			t = t->tleft;
		return clone(t->tleft);
	}
	if (tok == LOGBASE_F || tok == ROOT_F)
	{
		Tree* dl = simplify(diff(tr->tleft->tleft, vr)), * sol = to_tree(In2post2((tok == LOGBASE_F) ? "V/(U*ln(C))" : "V/(C*U^((C-1)/C))"));
		sol = remplace_var(remplace_var(remplace_var(sol, "U", tr->tleft->tleft), "V", dl), "C", tr->tleft->tright);
		clean_tree(dl);
		return sol;
	}
	Tree* dl = simplify(diff(tr->tleft, vr));
	Tree* sol = form_integral(sig, Derivtable, AMOUNT_DERIV);
	if (sol != NULL)
	{
		sol = remplace_var(remplace_var(sol, "U", tr->tleft), "V", dl);
		clean_tree(dl);
		return sol;
	}
	clean_tree(dl);
	return join(join(join(clone(tr), new_tree(vr), fnc[SEPARATEUR].ex), new_tree(vr), fnc[SEPARATEUR].ex), NULL, fnc[DERIV_F].ex);
}