/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing conditional pointer mutation does not emit unconditional relational ensures."
*/

#include <limits.h>

int input;
int flag_input;
int result;

void maybe_add(int *p, int flag) {
  if (flag) {
    *p = *p + 1;
  }
}

/*@
  requires INT_MIN <= input < INT_MAX;
  ensures flag_input != 0 ==> result == input+1;
  ensures flag_input == 0 ==> result == input;
*/
int main() {
  int x = input;

  maybe_add(&x, flag_input);

  result = x;

  return 0;
}
