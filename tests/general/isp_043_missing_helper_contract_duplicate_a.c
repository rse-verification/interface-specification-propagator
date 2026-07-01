/* run.config
OPT: -autoload-plugins -isp-missing-helper-contracts isp_043_missing_helper_contract_duplicate_b.c
COMMENT: "Testing missing helper report with duplicate static helper names."
*/

static void helper(int *p) {
  *p = *p + 1;
}

/*@
  ensures \result >= 0;
*/
int main(void) {
  int x = 0;
  helper(&x);
  return x;
}
