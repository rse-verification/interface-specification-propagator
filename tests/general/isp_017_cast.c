/* run.config
OPT: -autoload-plugins -isp -isp-print
COMMENT: "Testing cast expressions."
*/

int X;
long Y;

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(&X);
    requires \valid_read(&Y);
    requires \valid(&Y);
    requires X == 1;
    ensures Y == 1;
    assigns Y;
    */
void main() {
  if (X < 3)
    Y = (long)X;
}
