#include "units.hxx"

int main() {
  auto x = units::to_unit<"m/s*kg^2/Q">(19.1);
}