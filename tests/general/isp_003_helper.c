/* run.config
OPT: -autoload-plugins -isp -isp-print
COMMENT: "Testing contract inference for helper functions"
*/

int one() {
  return 1;
}

int two() {
  int a = one();
  int b = one();
  return a + b;
}

int main() {
  return two();
}
