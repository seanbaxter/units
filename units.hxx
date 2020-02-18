#pragma once
#include <string>
#include <cstdarg>
#include <optional>
#include <iostream>
#include <type_traits>

namespace units {

// Include printf-style string formatting to make it easy to throw
// nice error messages from the unit parser.

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

////////////////////////////////////////////////////////////////////////////////

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

// Generate a switch with a case statement for each enumerator in
// enum_t. On a match, invoke f() and pass an instance of the type associated
// with that enum.
template<typename enum_t, typename func_t>
bool enum_f(enum_t e, func_t f) {
  static_assert(__is_typed_enum(enum_t), 
    "template argument of enum_f must be a typed enum");

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

template<int... powers>
const char* make_symbol();

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

template<Arithmetic type_t, int... powers> 
struct unit_t {
  static_assert(sizeof...(powers) == dim_count);

  // Return a user-readable string describing the unit. This 
  // computation is performed at compile time using meta execution.
  static const char* symbol() {
    return make_symbol<powers...>();
  }

  // #include <compare> (included with the Circle compiler) to enable 
  // all relational operators.
  template<typename type2_t>
  constexpr auto operator<=>(const unit_t<type2_t, powers...>& rhs) const {
    return data <=> rhs.data;
  }

  // Have to define both <=> and == because a user-provided <=> doesn't 
  // automatically generate the relational operators.
  // However, a user-provided operator== will generate operator!=.
  template<typename type2_t>
  constexpr auto operator==(const unit_t<type2_t, powers...>& rhs) const {
    return data == rhs.data;
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

  template<Arithmetic type2_t>
  constexpr unit_t& operator*=(type2_t rhs) {
    data *= rhs;
    return *this;
  }

  // unit / unit
  // Note the subtraction of powers when dividing by a unit_t.
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
  // Note the inversion of powers when dividing by a unit_t.
  template<Arithmetic type2_t>
  friend constexpr auto operator/(type2_t lhs, const unit_t& rhs) ->
    unit_t<decltype(lhs / std::declval<type_t>()), -powers...> {

    return { lhs / rhs.data };
  }

  template<Arithmetic type2_t>
  constexpr unit_t& operator/=(type2_t rhs) {
    data /= rhs;
    return *this;
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
    return (... && (powers == powers2...[:]));
  }

  static bool compare_powers(const int(&powers2)[dim_count]) {
    return (... && (powers == powers2...[:]));
  }

  static void write_powers(int(&powers2)[dim_count]) {
    powers2...[:] = powers ...;
  }

  // streaming.
  friend std::ostream& operator<<(std::ostream& os, const unit_t& rhs) {
    os<< rhs.data<< " "<< symbol();
    return os;
  }

  // Allow explicit conversion to bool even for non-scalars.
  constexpr explicit operator bool() const {
    return 0 != data;
  }

  // Allow implicit conversion when the type is a scalar.
  template<typename type2_t>
  constexpr operator type2_t() const requires((... && (powers == 0))){
    return (type2_t)data;
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

// Define basic units with integer unit_t types. During any multiplication
// or division operator, these are promoted to the common arithmetic
// type.

inline constexpr meter_t<int> m { 1 };
inline constexpr auto m2 = m * m;
inline constexpr auto m3 = m * m2;

inline constexpr kg_t<int> kg { 1 };
inline constexpr auto kg2 = kg * kg;
inline constexpr auto kg3 = kg * kg2;

inline constexpr second_t<int> s { 1 };
inline constexpr auto s2 = s * s;
inline constexpr auto s3 = s * s2;

inline constexpr A_t<int> A { 1 };
inline constexpr auto A2 = A * A;
inline constexpr auto A3 = A * A2;

inline constexpr K_t<int> K { 1 };
inline constexpr auto K2 = K * K;
inline constexpr auto K3 = K * K2;

inline constexpr mol_t<int> mol { 1 };
inline constexpr auto mol2 = mol * mol;
inline constexpr auto mol3 = mol * mol2;;

inline constexpr cd_t<int> cd { 1 }; 
inline constexpr auto cd2 = cd * cd;
inline constexpr auto cd3 = cd * cd2;

// https://en.wikipedia.org/wiki/SI_derived_unit
inline constexpr auto Hz = 1 / s;
inline constexpr auto rad = m / m;
inline constexpr auto sr = m2 / m2;
inline constexpr auto N = kg * m / s2;
inline constexpr auto Pa = N / m2;
inline constexpr auto J = m * N;
inline constexpr auto W = J / s;
inline constexpr auto C = s * A;
inline constexpr auto V = W / A;
inline constexpr auto F = C / V;
inline constexpr auto ohm = V / A;
inline constexpr auto S = 1 / ohm;
inline constexpr auto Wb = J / A;
inline constexpr auto T = V * s / m2;
inline constexpr auto H = V * s / A;
inline constexpr auto lm = cd * sr;
inline constexpr auto lx = lm / m2;
inline constexpr auto Bq = 1 / s;
inline constexpr auto Gy = J / kg;
inline constexpr auto Sv = J / kg;
inline constexpr auto kat = mol / s;

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

// Could provide user-defined literals for all derived units.

} // namespace literals

namespace constants {

using namespace units;

// https://en.wikipedia.org/wiki/Physical_constant#Table_of_physical_constants
inline constexpr auto Na = 6.02214076e23 / mol;
inline constexpr auto kB = 1.380649e-23 * J / K;
inline constexpr auto e = 1.602176634e-19 * C;
inline constexpr auto G = 6.6743015e-11 * m3 / kg / s2;
inline constexpr auto h = 6.62607015e-34 * J * s;
inline constexpr auto c = 299792458.0 * m / s;
inline constexpr auto eps0 = 8.854187812813e-12 * F / m;
inline constexpr auto mu0 = 1.25266370621219e-6 * N / (A * A);
inline constexpr auto me = 9.109383701528e-31 * kg;
inline constexpr auto mp = 1.6726219236951e-27 * kg;
inline constexpr auto alpha = 7.297352569311e-3;
inline constexpr auto Kj = 483597.8484e9;
inline constexpr auto R = 8.314462618 * J / mol / K;
inline constexpr auto Rinf = 10973731.56816021 / m;
inline constexpr auto Rk = 258122.80745 * ohm;

} // namespace constants

// Parse an input string against the SI derived and fundamental units.
// Return the powers in the output array.
inline void parse_symbol(const char* s, int(&powers)[dim_count]) {
  const char* begin = s;
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
      throw throw_format("%s\n%*s^\nexpected '*' or '/' in unit specifier", 
        begin, s - begin, "");

    // Scan to the end of the token.
    const char* s2 = s;
    while(*s2 && '*' != *s2 && '/' != *s2 && '^' != *s2)
      ++s2;

    // Match the token spelling against the SI unit enums.
    std::string spec(s, s2);
    int powers2[dim_count] { };

    if(auto e = string_to_enum<dim_t>(spec.c_str())) {
      // After matching a fundamental unit, increment that power.
      powers2[(int)*e] = 1;

    } else if(s2 == s) {
      throw throw_format("%s\n%*s^\nexpected SI unit name in unit specifier", 
        begin, s - begin, "");

    } else if(auto e2 = string_to_enum<derived_t>(spec.c_str())) {
      // After matching a derived unit, update all the powers. This requires
      // entering a switch over all the derived units in derived_t, and on
      // our match we can invoke the static member function write_powers to
      // write the compile-time powers into powers2 array.
      enum_f(*e2, [&](auto x) { x.write_powers(powers2); });

    } else {
      throw throw_format("%s\n%*s^\nunrecognized unit name '%s' in unit specifier", 
        begin, s - begin, "", spec.c_str());
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
      throw throw_format("%s\n%*s^\ncannot parse power in unit specifier", 
        begin, s - begin, "", spec.c_str());
      
      s += digits;
    }

    if(negative)
      count = -count;

    // Accumulate the power.
    powers...[:] += count * powers2...[:] ...;
  }
}

// Parse a string non-type template parameter and return the corresponding
// unit type with the provided argument.
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

// Search the derived units and fundamental units to make a canonical
// formatted string describing the unit with these powers.
inline std::string make_symbol(const int(&powers)[dim_count]) {
  // Attempt to match against the derived units. These must match exactly.
  // Otherwise SI fundamental units are used.
  @meta for enum(auto derived : derived_t) {
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

} // namespace units
