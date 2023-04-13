////////////////////////////////////////
// { CASYMBA } { 0.1.0 }
// Author: Hamza.S, Adriweb, Hayleia, critor, Bisam
// License: CC-BY-NC-SA 4.0
// Description: symbolic simplify
////////////////////////////////////////

#include "calculs.h"

#ifdef _EZ80

static const Help use_function[] =
{
    { "Derivative", "sin(X),X,X)", "sin(X),X,2)", "X+2Y,X,Y)" },
    { "Primitive", "Expr1,var,var,var)", "sin(6X),X,X,X)", "" },
    { "Equa diff", "Y''-Y'-2Y=sin(2X),X,Y)", "Y'+2Y=-5*e^(-2X) and Y(0)=1,X,Y)", "" },
    { "Tangent", "Expr1,var,point)", "e^(X),X,1)", ""},
    { "reste : remain 2 Poly", "poly1,poly2,var)", "X^3-6X^2+11X-6,X^2-6X+8,X)", "" },
    { "quotient 2 Poly", "poly1,poly2,var)", "X^3-6X^2+11X-6,X^2-6X+8,X)", "" },
    { "gcd 2 Poly", "poly1,poly2,var)", "X^3-6X^2+11X-6,X^2-6X+8,X)", "" },
    { "simplify 2 Poly", "poly1,poly2,var)", "X^3-6X^2+11X-6,X^2-6X+8,X)", "" },
    { "Dev. / expand", "Expr1)", "(A+B)^2)", ""},
    { "facteur premier/prime factorization", "POSITIVE_INTEGER)", "45)", "" },
    { "Dev. limite / Taylor", "Expr1,var,ordre,point)", "sin(X),X,3,0)", "" }
};

void help(void)
{
    const Help* element;
    int k = 0;
    for (element = use_function; element != element + sizeof(use_function) / sizeof(use_function[0]) - 1; element++)
    {
        uint8_t  tok_len = 0;
        uint24_t tokstr_len = 0;

        void* data_ptr = ti_table[DERIV_F + k].ex;
        char* tokstr = ti_GetTokenString(&data_ptr, &tok_len, &tokstr_len);
        os_ClrHome();
        os_PutStrFull(element->utility);
        os_NewLine();
        os_PutStrLine(tokstr);
        os_PutStrFull(element->example0);
        os_NewLine();
        os_PutStrLine(tokstr);
        os_PutStrFull(element->example1);
        if (strlen(element->example2) != 0)
        {
            os_NewLine();
            os_PutStrLine(tokstr);
            os_PutStrFull(element->example2);
        }
        while (!(os_GetCSC()));
        k++;
        if (k == 10)
            break;
    }
}

static unsigned char* trim(const unsigned char* input, unsigned input_len, unsigned* trimmed_len) {
    unsigned i, trim_index = 0;
    unsigned char* trimmed;

    *trimmed_len = 0;

    for (i = 0; i < input_len; i++) {
        if (input[i] != OS_TOK_SPACE)
            (*trimmed_len)++;
    }

    trimmed = calloc(*trimmed_len + 1, sizeof(char));

    for (i = 0; i < input_len; i++) {
        if (input[i] != OS_TOK_SPACE)
            trimmed[trim_index++] = input[i];
    }

    return trimmed;
}

static unsigned char* read_ans_tokens(size_t* ans_len) {
    uint8_t type;
    string_t* ans = os_GetAnsData(&type);
    if (ans == NULL || type != OS_TYPE_STR) {
        *ans_len = 0;
        return NULL;
    }
    return trim((const unsigned char*)ans->data, ans->len, ans_len);
}

int main(void)
{
    unsigned char* str_in = NULL;
    unsigned ans_len = 0;

    str_in = read_ans_tokens(&ans_len);

    if (!str_in)
    {
        os_ClrHome();
        os_PutStrFull("Remplir Rep. d'abord");
        os_NewLine();
        os_PutStrFull("Fill Ans. variable first");
        os_NewLine();
        while (!(os_GetCSC()));
        return 1;
    }

    if (str_in[0] == (uint8_t)0xAF)
    {
        os_ClrHome();
        os_PutStrFull("Aide du programme. Pressez une touche...");
        os_NewLine();
        os_PutStrFull("Program help. Press a key...");
        while (!(os_GetCSC()));
        help();
        return 0;
    }
    DList rpn = In2post(str_in, ans_len);
    if (rpn == NULL)
    {
        os_ClrHome();
        os_PutStrFull("syntax error");
        while (!(os_GetCSC()));
        return 1;
    }
    Tree* tr = to_tree(rpn);
    Tree* simp = analyse(tr);
    if (simp == NULL)
    {
        os_ClrHome();
        if (Error != NULL)
        {
            DListCell* element = Error->begin;
            while (element != NULL)
            {
                os_PutStrFull(element->value);
                os_NewLine();
                element = element->next;
            }
            Error = clear_dlist(Error);
        }
        else
        {
            os_PutStrFull("Erreur.");
            os_NewLine();
        }
        while (!(os_GetCSC()));
        return 1;
    }
    string out_tokens = Post2in(simp);
    clean_tree(simp);
    os_NewLine();

    string out_tokens_tmp = out_tokens;
    uint16_t out_len = strlen(out_tokens);
    uint16_t real_out_tok_len = 0;
    while (out_len > 0) {
        uint8_t tok_len = 0;
        ti_GetTokenString((void**)&out_tokens_tmp, &tok_len, NULL);
        if (tok_len == 1 || tok_len == 2) {
            out_len -= tok_len;
            real_out_tok_len += tok_len;
        }
        else {
            break;
        }
    }

    string_t* out_str_for_ans = malloc(offsetof(string_t, data) + real_out_tok_len);
    if (out_str_for_ans) {
        out_str_for_ans->len = real_out_tok_len;
        memcpy(out_str_for_ans->data, out_tokens, real_out_tok_len);
        ti_SetVar(OS_TYPE_STR, OS_VAR_ANS, out_str_for_ans);
        ti_SetVar(OS_TYPE_STR, OS_VAR_Y2, out_str_for_ans);
        free(out_str_for_ans);
    }

    // todo: add it to the history in mathprint. see with commandz
    return 0;
}

#else

int main(int argc, char const* argv[])
{
    (void)argc;
    (void)argv;

    char ex[] = { 0x10, '3', 0xF1, '2', '7', 0x11 };
    DList rpn = In2post(ex, 6);
    Tree* tr = to_tree(rpn);
    Tree* simp = analyse(tr);
    string expr = Post2in2(simp);
    print_tree_prefix(simp);
    clean_tree(simp);
    printf("\nla forme simplifiee : %s\n", expr);
    free(expr);
    /*DList rpn = In2post2("diff(tan(2*x),x)");
    if (rpn == NULL)
    {
        printf("Erreur syntaxe\n");
        return 1;
    }
    Tree* tr = to_tree(rpn);

    print_tree_prefix(tr);

    printf("\n\n partie simplification :\n");

    Tree* simp = analyse(tr);
    if (simp == NULL)
    {
        if (Error != NULL)
        {
            DListCell* element = Error->begin;
            while (element != NULL)
            {
                puts(element->value);
                element = element->next;
            }
            Error = clear_dlist(Error);
        }
        else
        {
            puts("Erreur.");
        }
        return 1;
    }
    string expr = Post2in2(simp);
    print_tree_prefix(simp);
    clean_tree(simp);
    printf("\nla forme simplifiee : %s\n", expr);
    free(expr);*/
    return 0;
}

#endif // _EZ80
