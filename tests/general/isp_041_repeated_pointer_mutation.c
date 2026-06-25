/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing repeated pointer mutation skips single-write arithmetic safety inference."
*/

#include <limits.h>

int input;
int result;

void add_twice(int *p) {
  *p = *p + 1;
  *p = *p + 1;
}

/*@
  requires INT_MIN < input < INT_MAX-1;
  ensures result == input+2;
*/
int main() {
  int x = input;

  add_twice(&x);

  result = x;

  return 0;
}
