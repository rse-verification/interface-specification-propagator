/* run.config
OPT: -no-check -autoload-plugins -isp -isp-print
COMMENT: "Test for switch statements."
*/

int DB[5];

typedef enum { RPM, SPEED, TEMPERATURE, HUMIDITY, PRESSURE } PARAMETER;

PARAMETER X;

int read_db(PARAMETER p) {
  return DB[p];
}

/*@ behavior interface_spec:
    assumes \true;
    requires \valid_read(DB+(0..4));
    requires DB[RPM] ∈ (0..9000);
    requires DB[SPEED] ∈ (0..400);
    requires DB[TEMPERATURE] ∈ (0..400);
    requires DB[HUMIDITY] ∈ (0..100);
    requires DB[PRESSURE] ∈ (0..150);
    requires X ∈ {RPM, SPEED, PRESSURE};
    assigns \nothing;
    */
void main() {
  switch (X) {
    case RPM:
      read_db(RPM);
      break;

    case SPEED:
      read_db(SPEED);
      break;

    case TEMPERATURE:
      read_db(TEMPERATURE);
      break;

    case HUMIDITY:
      read_db(HUMIDITY);
      break;

    case PRESSURE:
      read_db(PRESSURE);
      break;

    default:
      break;
  }
}
