/* run.config
OPT: -autoload-plugins -isp -isp-print
COMMENT: "Testing inference for mutated global variables"
*/

int X;

int main() {
  X = 2;
  return X;
}
