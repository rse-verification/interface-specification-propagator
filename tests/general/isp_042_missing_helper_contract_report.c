/* run.config
OPT: -autoload-plugins -isp-missing-helper-contracts
COMMENT: "Testing Frama-C based missing helper contract report."
*/

void helper(int *p) {
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
