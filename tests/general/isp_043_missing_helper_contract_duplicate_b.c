/* run.config
OPT: -no-check -autoload-plugins
COMMENT: "Pointer helper."
*/

static void helper(int *p) {
  *p = *p + 2;
}
