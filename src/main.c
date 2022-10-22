////////////////////////////////////////
// { CASYFO } { 0.0.1 }
// Author: Hamza.S, Adriweb, Hayleia, critor, Bisam
// License:
// Description: symbolic simplify
////////////////////////////////////////

#include "calculs.h"

#ifdef _EZ80

static unsigned char *trim(const unsigned char *input, unsigned input_len, unsigned *trimmed_len) {
    unsigned i, trim_index = 0;
    unsigned char *trimmed;

    *trimmed_len = 0;

    for(i = 0; i < input_len; i++) {
        if(input[i] != OS_TOK_SPACE)
            (*trimmed_len)++;
    }

    trimmed = calloc(*trimmed_len + 1, sizeof(char));

    for(i = 0; i < input_len; i++) {
        if(input[i] != OS_TOK_SPACE)
            trimmed[trim_index++] = input[i];
    }

    return trimmed;
}

static unsigned char* read_ans_tokens(size_t* ans_len) {
    uint8_t type;
    string_t *ans = os_GetAnsData(&type);
    if (ans == NULL || type != OS_TYPE_STR) {
        *ans_len = 0;
        return NULL;
    }
    return trim((const unsigned char *)ans->data, ans->len, ans_len);
}

int main(void)
{
    unsigned char* str_in = NULL;
    unsigned ans_len = 0;

    str_in = read_ans_tokens(&ans_len);
    DList rpn = In2post(str_in, ans_len);
    Tree* tr = to_tree(rpn);
    Tree* simp = analyse(tr);

    string out_tokens = Post2in(simp);
    clean_tree(simp);
    os_NewLine();

    string out_tokens_tmp = out_tokens;
    uint16_t out_len = strlen(out_tokens);
    uint16_t real_out_tok_len = 0;
    while(out_len > 0) {
        uint8_t tok_len = 0;
        ti_GetTokenString((void**)&out_tokens_tmp, &tok_len, NULL);
        if (tok_len == 1 || tok_len == 2) {
            out_len -= tok_len;
            real_out_tok_len += tok_len;
        } else {
            break;
        }
    }

    string_t *out_str_for_ans = malloc(offsetof(string_t, data) + real_out_tok_len);
    if (out_str_for_ans) {
        out_str_for_ans->len = real_out_tok_len;
        memcpy(out_str_for_ans->data, out_tokens, real_out_tok_len);
        ti_SetVar(OS_TYPE_STR, OS_VAR_ANS, out_str_for_ans);
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

	DList rpn = In2post("3.1415926535898"); // 
	Tree* tr = to_tree(rpn);
	
	print_tree_prefix(tr);

	printf("\n\n partie simplification :\n");

	Tree* simp = analyse(tr);
	string expr = Post2in(simp);
	print_tree_prefix(simp);
	clean_tree(simp);
	printf("\nla forme simplifiee : %s\n", expr);

	return 0;
}

#endif
