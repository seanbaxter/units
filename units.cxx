#include "units.hxx"

@meta printf("SI fundamental units:\n");
@meta printf("  %s\n", @enum_names(units::dim_t))...;

@meta printf("SI derived units:\n");
@meta printf("  %s\n", @enum_names(units::derived_t))...;

@mauto print(const char* s) {
  return std::cout<< s<< " is "<< @@expression(s)<< "\n";
}

int main() {
  using namespace units;
  using namespace units::literals;

  auto c1 = 299782458.0 * m / s;
  print("c1");

  // User-defined literals always return double unit_t.
  auto c2 = 299782458.0_m / s;
  print("c2");

  // The type of the unit_t is inferred from its argument type.
  // The string template argument is parsed to yield the unit_t type.
  auto c3 = to_unit<"m/s">(299792458.0); 
  print("c3");

  auto c4 = to_unit<"m*s^-1">(299792458.0); 
  print("c4");

  // Declare with make_unit_t. Ugly when used as direct declaration, 
  // but possibly convenient for metaprogramming.
  auto c5 = make_unit_t<double, 
    power_t { dim_t::m, 1 }, 
    power_t { dim_t::s, -1 }
  > { 299792458.0 };
  print("c5");

  // The unit specifier parser supports negative powers.
  auto G1 = to_unit<"m^3*kg^-1*s^-2">(6.6743015e-11);
  print("G1");

  // It also supports positive powers after slashes.
  auto G2 = to_unit<"m^3/kg/s^2">(6.6743015e-11);
  print("G2");

  // Prints as 15.3 J.
  auto e1 = 15.3 * J;
  print("e1");

  // Also prints as 15.3 J. Joule is a registered derived type, so
  // any unit_t that exactly matches that unit is printed as J.
  auto e2 = 15.3 * kg * m2 / s2;
  print("e2");
}