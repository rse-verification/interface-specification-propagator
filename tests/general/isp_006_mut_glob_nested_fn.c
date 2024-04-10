/* run.config
OPT: -autoload-plugins -isp -isp-print
COMMENT: "Testing inference for mutated global variables in nested function
calls."
*/

int X;

void assign_x(int x) {
  X = x;
}

int one() {
  return 1;
}

int two() {
  int a, b, c;
  a = one();
  b = one();
  c = a + b;
  assign_x(c);
  return c;
}

int main() {
  int a, b, c;
  a = one();
  b = two();
  c = a + b;
  return c;
}
