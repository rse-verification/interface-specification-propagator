/* run.config
EXIT: 1
OPT: -autoload-plugins -isp -isp-print -main calculate
COMMENT: "Show over approximation of EVA."
*/

int X;
int Y;

/*@ requires \valid_read(&Y);
    requires \valid_read(&X);
    requires X \in (0..10);
    requires Y \in (0..20);
 */
int calculate() {
  if (Y > X)
    return 0;
  else
    return X - Y;
}