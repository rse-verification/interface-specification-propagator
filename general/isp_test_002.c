/* run.config
OPT: -autoload-plugins -isp
COMMENT: "For testing unreachable function detection"
*/

int main() {
  return 0;
}

int add(int x, int y) {
  return x + y;
}