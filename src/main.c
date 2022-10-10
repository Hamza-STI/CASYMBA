#include "calculs.h"

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
