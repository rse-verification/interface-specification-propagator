/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Testing if statements."
*/

int X;
int Y;

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires \valid_read(&Y);
    requires \valid(&Y);
    requires X ∈ {1, 2, 3, 4, 5};
    assigns Y;
    */
void main() {
  if (X < 3)
    Y = X;
  else
    Y = 2 * X;
}
