#include <string>
#include <cstdarg>
#include <optional>
#include <iostream>
#include <type_traits>

inline std::string vformat(const char* pattern, va_list args) {
  va_list args_copy;
  va_copy(args_copy, args);

  int len = std::vsnprintf(nullptr, 0, pattern, args);
  std::string result(len, ' ');
  std::vsnprintf(result.data(), len + 1, pattern, args_copy);
 
  va_end(args_copy);
  return result;
}

inline std::string format(const char* pattern, ...) {
  va_list args;
  va_start(args, pattern);
  std::string s = vformat(pattern, args);
  va_end(args);
  return s;
}

inline void throw_format(const char* pattern, ...) {
  va_list args;
  va_start(args, pattern);
  std::string s = vformat(pattern, args);
  va_end(args);
  throw std::runtime_error(s);
}

template<typename enum_t>
const char* enum_to_string(enum_t e) {
  switch(e) {
    @meta for enum(enum_t e2 : enum_t)
      case e2:
        return @enum_name(e2);

    default:
      return nullptr;
  }
}

template<typename enum_t>
std::optional<enum_t> string_to_enum(const char* s) {
  @meta for enum(enum_t e : enum_t)
    if(0 == strcmp(@enum_name(e), s))
      return e;

  return { };
}

template<typename enum_t, typename func_t>
bool enum_f(enum_t e, func_t f) {
  switch(e) {
    @meta for enum(enum_t e2 : enum_t) {
      case e2:
        f(@enum_type(e2)());
        return true;
    }

    default:
      return false;
  }
}

template<typename type_t>
concept Arithmetic = std::is_arithmetic<type_t>::value;

// Sort dimensions according to this order. Non-negative
// units go first, then negative units as denominators.

// Relate to fundamental types.
enum class dim_t {
  m,    // length
  kg,   // mass
  s,    // time
  A,    // current
  K,    // temperature
  mol,  // amount
  cd,   // luminous intensity
};
constexpr size_t dim_count = @enum_count(dim_t);

template<int... powers>
const char* make_symbol();

template<Arithmetic type_t, int... powers> 
struct unit_t {
  static_assert(sizeof...(powers) == dim_count);

  // Return a user-readable string describing the unit. This 
  // computation is performed at compile time using meta execution.
  static const char* symbol() {
    return make_symbol<powers...>();
  }

  // unit * unit
  template<Arithmetic type2_t, int... powers2>
  constexpr auto operator*(const unit_t<type2_t, powers2...>& rhs) const ->
    unit_t<decltype(std::declval<type_t>() * rhs.data), powers + powers2...> {

    return { data * rhs.data };
  }

  // Unit * arithmetic
  template<Arithmetic type2_t>
  constexpr auto operator*(type2_t x) const -> 
    unit_t<decltype(std::declval<type_t>() * x), powers...> {

    return { data * x };
  }

  // Arithmetic * unit
  template<Arithmetic type2_t>
  friend constexpr auto operator*(type2_t lhs, const unit_t& rhs) ->
    unit_t<decltype(lhs * std::declval<type_t>()), powers...> {

    return { lhs * rhs.data };
  }

  // unit / unit
  template<Arithmetic type2_t, int... powers2>
  constexpr auto operator/(const unit_t<type2_t, powers2...>& rhs) const ->
    unit_t<decltype(std::declval<type_t>() / rhs.data), powers - powers2...> {

    return { data / rhs.data };
  }

  // unit / Arithmetic
  template<Arithmetic type2_t>
  constexpr auto operator/(type2_t x) const -> 
    unit_t<decltype(std::declval<type_t>() / x), powers...> {

    return { data / x };
  }

  // Arithmetic / unit
  template<Arithmetic type2_t>
  friend constexpr auto operator/(type2_t lhs, const unit_t& rhs) ->
    unit_t<decltype(lhs / std::declval<type_t>()), powers...> {

    return { lhs / rhs.data };
  }

  constexpr unit_t operator-() const {
    return { -data };
  }

  template<Arithmetic type2_t>
  constexpr auto operator+(const unit_t<type2_t, powers...>& rhs) const ->
    unit_t<decltype(std::declval<type_t>() + rhs.data), powers...> {

    return { data + rhs.data };
  }

  template<Arithmetic type2_t>
  constexpr auto operator-(const unit_t<type2_t, powers...>& rhs) const ->
    unit_t<decltype(std::declval<type_t>() - rhs.data), powers...> {

    return { data - rhs.data };
  }

  template<typename type2_t, int... powers2>
  static bool compare_powers() {
    return (... && (powers...[:] == powers2...[:]));
  }

  static bool compare_powers(const int(&powers2)[dim_count]) {
    return (... && (powers...[:] == powers2...[:]));
  }

  static void write_powers(int(&powers2)[dim_count]) {
    powers2...[:] = powers...[:] ...;
  }

  // streaming.
  friend std::ostream& operator<<(std::ostream& os, const unit_t& rhs) {
    os<< rhs.data<< " "<< symbol();
    return os;
  }

  // Allow implicit conversion when the type is a scalar.
  constexpr operator type_t() const {
    static_assert((... && (0 == powers...[:])), 
      "implicit conversion from unit_t only allowed for unitless types"); 

    return data;
  }

  // Allow explicit conversion to a different numeric type.
  template<typename type2_t>
  constexpr unit_t<type2_t, powers...> convert() const {
    return { (type2_t)data };
  }

  type_t data;
};

// Compute a sum of the powers on each type.
struct power_t {
  dim_t dim;
  int power;    // Should be non-zero.
};

template<typename type_t, power_t... powers>
struct unit_builder_t {
  // Accumulate the exponent on each specified dimension into a 
  // compile-time buffer.
  @meta int dims[dim_count] { };
  @meta dims[(int)powers.dim] += powers.power ...;

  // Use the ranks to typedef a unit_t.
  typedef unit_t<type_t, dims...[:] ...> type;
};

template<typename type_t, auto... powers>
using make_unit_t = typename unit_builder_t<type_t, powers...>::type;

// SI units

// meter
template<typename type_t = double>
using meter_t = make_unit_t<type_t, power_t { dim_t::m, 1 }>;

// We can also use pack expansion to specify the ranks directly:
// using meter_t = unit_t<type_t, @enum_values(dim_t) == dim_t::m ...>;

// second
template<typename type_t = double>
using second_t = make_unit_t<type_t, power_t { dim_t::s, 1 }>;

// kg
template<typename type_t = double>
using kg_t = make_unit_t<type_t, power_t { dim_t::kg, 1 }>;

// A
template<typename type_t = double>
using A_t = make_unit_t<type_t, power_t { dim_t::A, 1 }>;

// K
template<typename type_t = double>
using K_t = make_unit_t<type_t, power_t { dim_t::K, 1 }>;

// mol
template<typename type_t = double>
using mol_t = make_unit_t<type_t, power_t { dim_t::mol, 1 }>;

// cd
template<typename type_t = double>
using cd_t = make_unit_t<type_t, power_t { dim_t::cd, 1 }>;

namespace units {

// Define basic units with integer unit_t types. During any multiplication
// or division operator, these are promoted to the common arithmetic
// type.

constexpr meter_t<int> m { 1 };
constexpr auto m2 = m * m;
constexpr auto m3 = m * m2;

constexpr kg_t<int> kg { 1 };
constexpr auto kg2 = kg * kg;
constexpr auto kg3 = kg * kg2;

constexpr second_t<int> s { 1 };
constexpr auto s2 = s * s;
constexpr auto s3 = s * s2;

constexpr A_t<int> A { 1 };
constexpr auto A2 = A * A;
constexpr auto A3 = A * A2;

constexpr K_t<int> K { 1 };
constexpr auto K2 = K * K;
constexpr auto K3 = K * K2;

constexpr mol_t<int> mol { 1 };
constexpr auto mol2 = mol * mol;
constexpr auto mol3 = mol * mol2;;

constexpr cd_t<int> cd { 1 }; 
constexpr auto cd2 = cd * cd;
constexpr auto cd3 = cd * cd2;

// https://en.wikipedia.org/wiki/SI_derived_unit
constexpr auto Hz = 1 / s;
constexpr auto rad = m / m;
constexpr auto sr = m2 / m2;
constexpr auto N = kg * m / s2;
constexpr auto Pa = N / m2;
constexpr auto J = m * N;
constexpr auto W = J / s;
constexpr auto C = s * A;
constexpr auto V = W / A;
constexpr auto F = C / V;
constexpr auto ohm = V / A;
constexpr auto S = 1 / ohm;
constexpr auto Wb = J / A;
constexpr auto T = V * s / m2;
constexpr auto H = V * s / A;
constexpr auto lm = cd * sr;
constexpr auto lx = lm / m2;
constexpr auto Bq = 1 / s;
constexpr auto Gy = J / kg;
constexpr auto Sv = J / kg;
constexpr auto kat = mol / s;

// These derived units will be recognized by the parser and also
// printed by the stringifier if the unit matches exactly.
enum typename class derived_t {
  Hz = decltype(Hz),
  N = decltype(N),
  Pa = decltype(Pa),
  J = decltype(J),
  W = decltype(W),
  C = decltype(C),
  V = decltype(V),
  F = decltype(F),
  ohm = decltype(ohm),
  S = decltype(S),
  Wb = decltype(Wb),
  T = decltype(T),
  H = decltype(H),
  lm = decltype(lm),
  lx = decltype(lx),
  kat = decltype(kat),
};

}

namespace literals {

meter_t<double> operator""_m(long double x) {
  return { (double)x };
}

kg_t<double> operator""_kg(long double x) {
  return { (double)x };
}

second_t<double> operator""_s(long double x) {
  return { (double)x };
}

A_t<double> operator""_A(long double x) {
  return { (double)x };
}

K_t<double> operator""_K(long double x) {
  return { (double)x };
}

mol_t<double> operator""_mol(long double x) {
  return { (double)x };
}

cd_t<double> operator""_cd(long double x) {
  return { (double)x };
}

}


namespace constants {

using namespace units;

// https://en.wikipedia.org/wiki/Physical_constant#Table_of_physical_constants
constexpr auto Na = 6.02214076e23 / mol;
constexpr auto kB = 1.380649e-23 * J / K;
constexpr auto e = 1.602176634e-19 * C;
constexpr auto G = 6.6743015e-11 * m3 / kg / s2;
constexpr auto h = 6.62607015e-34 * J * s;
constexpr auto c = 299792458.0 * m / s;
constexpr auto eps0 = 8.854187812813e-12 * F / m;
constexpr auto mu0 = 1.25266370621219e-6 * N / (A * A);
constexpr auto me = 9.109383701528e-31 * kg;
constexpr auto mp = 1.6726219236951e-27 * kg;
constexpr auto alpha = 7.297352569311e-3;
constexpr auto Kj = 483597.8484e9;
constexpr auto R = 8.314462618 * J / mol / K;
constexpr auto Rinf = 10973731.56816021 / m;
constexpr auto Rk = 258122.80745 * ohm;

}

// Parse an input string against the SI derived and fundamental units.
// Return the powers in the output array.
inline void parse_symbol(const char* s, int(&powers)[dim_count]) {
  bool expect_token = false;
  while(char c = *s) {
    bool negative = false;
    if('/' == c) {
      ++s;
      negative = true;

    } else if(!expect_token || '*' == c) {
      if(expect_token) ++s;
      expect_token = true;

    } else 
      throw throw_format("expected '*' or '/' at '%s'", s);

    // Scan to the end of the token.
    const char* s2 = s;
    while(*s2 && '*' != *s2 && '/' != *s2 && '^' != *s2)
      ++s2;

    // Match the token spelling against the SI unit enums.
    std::string spec(s, s2);
    int powers2[dim_count] { };

    if(auto e = string_to_enum<dim_t>(spec.c_str())) {
      // Check fundamental units.
      powers2[(int)*e] = 1;

    } else if(auto e2 = string_to_enum<units::derived_t>(spec.c_str())) {
      // Check derived units.
      enum_f(*e2, [&](auto x) { x.write_powers(powers2); });

    } else if(s2 == s) {
      throw throw_format("expected unit specifier at '%s'", s);

    } else {
      throw throw_format("unknown unit specifier '%s'", spec.c_str());
    }

    s = s2;
    int count = 1;
    if('^' == *s) {
      ++s;
      if('-' == *s) {
        ++s;
        negative = !negative;
      }

      int digits = sscanf(s, "%d", &count);
      if(digits <= 0)
        throw throw_format("cannot parse power at '%s', s");
      
      s += digits;
    }

    if(negative)
      count = -count;

    // Accumulate the power.
    powers...[:] += count * powers2...[:] ...;
  }
}

// 
inline std::string make_symbol(const int(&powers)[dim_count]) {
  // Attempt to match against the derived units. These must match exactly.
  // Otherwise SI fundamental units are used.
  @meta for enum(auto derived : units::derived_t) {
    if(@enum_type(derived)::compare_powers(powers)) {
      return @enum_name(derived);
    }
  }

  std::string s;

  // Print the positive symbols.
  for(size_t i = 0; i < dim_count; ++i) {
    int p = powers[i];
    if(p > 0) {
      if(s.size()) 
        s += "*";

      s += enum_to_string((dim_t)i);
      if(p > 1)
        s += "^" + std::to_string(p);
    }
  }

  // Print the negative symbols.
  for(size_t i = 0; i < dim_count; ++i) {
    int p = powers[i];
    if(p < 0) {
      s += "/";
      s += enum_to_string((dim_t)i);

      if(p < -1)
        s += "^" + std::to_string(-p);
    }
  }

  return s;
}

template<int... powers>
const char* make_symbol() {
  static_assert(sizeof...(powers) == dim_count);

  @meta const int powers2[] { powers... };
  return @string(make_symbol(powers2));
}

// Use return type deduction.
template<const char name[], typename type_t>
auto to_unit(type_t x) {
  // Parse the string non-type template parameter at compile time into an
  // array of powers.
  @meta int dims[dim_count] { };
  @meta parse_symbol(name, dims);

  // Expand the powers array into non-type template arguments.
  typedef unit_t<type_t, dims...[:] ...> unit_type;
  return unit_type { x };
}


@meta printf("SI fundamental units:\n");
@meta printf("  %s\n", @enum_names(dim_t))...;

@meta printf("SI derived units:\n");
@meta printf("  %s\n", @enum_names(units::derived_t))...;

@mauto print(const char* s) {
  return std::cout<< s<< " = "<< @@expression(s)<< " ("<< 
    @type_string(decltype(@@expression(s)))<< ")\n";
}

int main() {
  using namespace literals;
  using namespace units;

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

  // Declare with make_unit_t. Uglyfor direct declaration, but convenient
  // for meta programming.
  auto c5 = make_unit_t<double, 
    power_t { dim_t::m, 1 }, 
    power_t { dim_t::s, -1 }
  > { 299792458.0 };
  print("c5");

  // ERROR: implicit conversion from unit_t only allowed for unitless types
  // double scalar = c2; 

  // Allow implicit conversions from unitless types.
  double scalar = c2 / c1;

  auto G1 = to_unit<"m^3*kg^-1*s^-2">(6.6743015e-11);
  print("G1");

  auto G2 = to_unit<"m^3/akg/s^2">(6.6743015e-11);
  print("G1");

  // Prints as 15.3 J.
  auto e1 = 15.3 * J;
  print("e1");

  // Also prints as 15.3 J. Joule is a registered derived type, so
  // any unit_t that exactly matches that unit is printed as J.
  auto e2 = 15.3 * kg * m2 / s2;
  print("e2");
}