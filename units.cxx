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

template<typename type_t>
concept Arithmetic = std::is_arithmetic<type_t>::value;

// Sort dimensions according to this order. Non-negative
// units go first, then negative units as denominators.

// Relate to fundamental types.
enum class dim_t {
	m,		// length
	kg,		// mass
	s,		// time
	A,		// current
	K,		// temperature
	mol,	// amount
	cd,		// luminous intensity
};

@meta printf("Supported units:\n");
@meta printf("  %s\n", @enum_names(dim_t))...;

inline std::string make_symbol(const int(&powers)[@enum_count(dim_t)]) {
	const size_t count = @enum_count(dim_t);
	std::string s;

	// Print the positive symbols.
	for(size_t i = 0; i < count; ++i) {
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
	for(size_t i = 0; i < count; ++i) {
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

inline void parse_symbol(const char* s, int(&powers)[@enum_count(dim_t)]) {
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
		dim_t dim;
		if(auto e = string_to_enum<dim_t>(spec.c_str())) {
			dim = *e;

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
		powers[(int)dim] += count;
	}
}

template<int... powers>
const char* make_symbol() {
	static_assert(sizeof...(powers) == @enum_count(dim_t));

	@meta const int powers2[] { powers... };
	return @string(make_symbol(powers2));
}

template<Arithmetic type_t, int... powers> 
struct unit_t {
	static_assert(sizeof...(powers) == @enum_count(dim_t));

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
	int power;		// Should be non-zero.
};

template<typename type_t, power_t... powers>
struct unit_builder_t {
	@meta int dims[@enum_count(dim_t)] { };
	@meta dims[(int)powers.dim] += powers.power ...;

	typedef unit_t<type_t, dims...[:]...> type;
};

template<typename type_t, auto... powers>
using make_unit_t = typename unit_builder_t<type_t, powers...>::type;

// SI units

// meter
template<typename type_t = double>
using meter_t = make_unit_t<type_t, power_t { dim_t::m, 1 }>;

constexpr meter_t<int> meter { 1 }; 
constexpr auto meter2 = meter * meter;
constexpr auto meter3 = meter * meter2;

meter_t<double> operator""_m(long double x) {
	return { (double)x };
}

// second
template<typename type_t = double>
using second_t = make_unit_t<type_t, power_t { dim_t::s, 1 }>;

constexpr second_t<int> second { 1 };
constexpr auto second2 = second * second;
constexpr auto second3 = second * second2;


// Can't use _s because that's already reserved for strings.
second_t<double> operator""_sec(long double x) {
	return { (double)x };
}

// kg
template<typename type_t = double>
using kg_t = make_unit_t<type_t, power_t { dim_t::kg, 1 }>;

constexpr kg_t<int> kg { 1 };

kg_t<double> operator""_kg(long double x) {
	return { (double)x };
}

// Use return type deduction.
template<const char name[], typename type_t>
auto to_unit(type_t x) {
	// Parse the string non-type template parameter at compile time into an
	// array of powers.
	@meta int powers[@enum_count(dim_t)] { };
	@meta parse_symbol(name, powers);

	// Expand the powers array into non-type template arguments.
	typedef unit_t<type_t, powers...[:] ...> unit_type;
	return unit_type { x };
}

int main() {
	// User-defined literals always return double unit_t.
	auto c1 = 299782458.0_m / second;
	std::cout<< c1<< "\n";

	// The type of the unit_t is inferred from its argument type.
	// The string template argument is parsed to yield the unit_t type.
	auto c2 = to_unit<"m/s">(299792458.0); 
	std::cout<< c2<< "\n";

	// Declare with make_unit_t. Uglyfor direct declaration, but convenient
	// for meta programming.
	auto c3 = make_unit_t<double, power_t { dim_t::m, 1 }, 
		power_t { dim_t::s, -1 }> { 299792458.0 };
	std::cout<< c3<< "\n";

	auto m3 = meter * meter * meter.convert<double>();
	std::cout<< m3<< "\n";

	// ERROR: implicit conversion from unit_t only allowed for unitless types
	// double scalar = c2; 

	// Allow implicit conversions from unitless types.
	double scalar = c2 / c1;

	auto G = to_unit<"m^3*kg^-1*s^-2">(6.67408);
	std::cout<< G<< "\n";
}