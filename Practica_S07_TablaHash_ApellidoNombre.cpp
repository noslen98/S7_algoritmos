// =============================================================
// Practica N.o 07 - ACTIVIDAD 5 (C++17)
// Funcion hash personalizada (FNV-1a) y benchmark con unordered_map
// Compilar: g++ -std=c++17 -O2 -Wall -Wextra -o s07 Practica_S07_TablaHash_ApellidoNombre.cpp
// =============================================================
#include <unordered_map>
#include <string>
#include <vector>
#include <chrono>
#include <iostream>
#include <iomanip>
#include <random>
#include <algorithm>
#include <cmath>
#include <cassert>

using Clock = std::chrono::high_resolution_clock;

double mediana(std::vector<double> v) {
    std::sort(v.begin(), v.end());
    return v[v.size() / 2];
}
double ms_desde(Clock::time_point t0) {
    return std::chrono::duration<double, std::milli>(Clock::now() - t0).count();
}
template <class F>
double medir(F f, int repeticiones) {
    std::vector<double> t;
    for (int r = 0; r < repeticiones; ++r) {
        auto t0 = Clock::now();
        f();
        t.push_back(ms_desde(t0));
    }
    return mediana(t);
}

// ---------- Funcion hash personalizada: FNV-1a ----------
struct HashFNV {
    size_t operator()(const std::string& s) const {
        size_t hash = 14695981039346656037ULL;       // FNV offset basis
        for (char c : s) {
            hash ^= static_cast<size_t>(static_cast<unsigned char>(c));
            hash *= 1099511628211ULL;                // FNV prime
        }
        return hash;
    }
};

// ---------- Hash polinomial, el mismo de la Actividad 1 ----------
struct HashPolinomial {
    size_t operator()(const std::string& s) const {
        size_t h = 0, potencia = 1;
        for (char c : s) {
            h += static_cast<size_t>(static_cast<unsigned char>(c)) * potencia;
            potencia *= 31ULL;
        }
        return h;
    }
};

// ---------- Hash deliberadamente malo: suma de caracteres ----------
struct HashSuma {
    size_t operator()(const std::string& s) const {
        size_t h = 0;
        for (char c : s) h += static_cast<size_t>(static_cast<unsigned char>(c));
        return h;
    }
};

template <typename Hash>
double benchmarkHash(const std::vector<std::string>& claves, const char* nombre,
                     int repeticiones) {
    double ms = medir([&] {
        std::unordered_map<std::string, int, Hash> m;
        m.reserve(claves.size());
        for (int i = 0; i < static_cast<int>(claves.size()); i++) m[claves[i]] = i;
        long long suma = 0;
        for (const auto& k : claves) suma += m[k];     // se usa para que -O2 no lo elimine
        if (suma < 0) std::cout << "";                 // imposible, evita el aviso
    }, repeticiones);

    // Estadisticas de la tabla ya construida
    std::unordered_map<std::string, int, Hash> m;
    m.reserve(claves.size());
    for (int i = 0; i < static_cast<int>(claves.size()); i++) m[claves[i]] = i;
    size_t mayor = 0;
    for (size_t b = 0; b < m.bucket_count(); ++b) mayor = std::max(mayor, m.bucket_size(b));

    std::cout << "   " << std::setw(16) << std::left << nombre << std::right
              << std::setw(10) << ms << " ms"
              << std::setw(12) << m.load_factor() << " carga"
              << std::setw(8) << m.bucket_count() << " celdas"
              << std::setw(6) << mayor << " max\n";
    return ms;
}

// Mide la distribucion de una funcion hash sobre m celdas (igual que la Actividad 1)
template <typename Hash>
void distribucion(const std::vector<std::string>& claves, size_t m, const char* nombre) {
    std::vector<int> tabla(m, 0);
    Hash h;
    for (const auto& k : claves) tabla[h(k) % m]++;
    size_t ocupadas = 0;
    int maximo = 0;
    for (int c : tabla) {
        if (c > 0) ocupadas++;
        maximo = std::max(maximo, c);
    }
    double promedio = static_cast<double>(claves.size()) / static_cast<double>(m);
    double var = 0;
    for (int c : tabla) var += (c - promedio) * (c - promedio);
    var /= static_cast<double>(m);
    std::cout << "   " << std::setw(16) << std::left << nombre << std::right
              << std::setw(8) << ocupadas << "/" << m << " ocupadas"
              << std::setw(6) << maximo << " max"
              << std::setw(10) << std::sqrt(var) / promedio << " CV\n";
}

int main() {
    std::cout << std::fixed << std::setprecision(3);
    const int R = 7;

    // ---------- Generacion de claves ----------
    std::mt19937 rng(42);
    const std::string chars = "abcdefghijklmnopqrstuvwxyz";
    std::vector<std::string> claves;
    const int N = 50000;
    for (int i = 0; i < N; i++) {
        std::string s(8, ' ');
        for (char& c : s) c = chars[rng() % 26];
        claves.push_back(s);
    }

    // ---------- 1. Verificacion de la funcion FNV-1a ----------
    HashFNV fnv;
    assert(fnv("abc") == fnv("abc"));                 // determinista
    assert(fnv("abc") != fnv("abd"));                 // sensible al cambio
    assert(fnv("amor") != fnv("roma"));               // sensible al orden
    std::cout << "1. FNV-1a: determinista y sensible al orden: OK\n";
    std::cout << "   h(\"amor\") = " << fnv("amor") << "\n";
    std::cout << "   h(\"roma\") = " << fnv("roma") << "\n\n";

    // ---------- 2. Distribucion sobre una tabla de 1009 celdas ----------
    std::cout << "2. DISTRIBUCION (n = " << N << " claves, m = 1009 celdas)\n";
    distribucion<std::hash<std::string>>(claves, 1009, "std::hash");
    distribucion<HashFNV>(claves, 1009, "FNV-1a");
    distribucion<HashPolinomial>(claves, 1009, "polinomial p=31");
    distribucion<HashSuma>(claves, 1009, "suma (malo)");
    std::cout << "   CV de referencia de un hash uniforme ideal: "
              << std::sqrt((1.0 - 1.0 / 1009) * 1009 / N) << "\n\n";

    // ---------- 3a. Costo PURO de la funcion hash ----------
    // El benchmark con unordered_map esta dominado por la reserva de memoria,
    // que oculta las diferencias entre funciones hash. Aqui se mide solo el
    // calculo del hash sobre las mismas claves.
    std::cout << "3a. COSTO PURO DE LA FUNCION HASH (n = " << N
              << ", 20 pasadas)\n";
    auto costo_puro = [&](auto h, const char* nombre) {
        double ms = medir([&] {
            size_t acc = 0;
            for (const auto& k : claves) acc += h(k);
            if (acc == 1) std::cout << "";          // impide la eliminacion
        }, 20);
        std::cout << "   " << std::setw(16) << std::left << nombre << std::right
                  << std::setw(9) << ms << " ms"
                  << std::setw(10) << ms * 1e6 / N << " ns/clave\n";
        return ms;
    };
    double p_std = costo_puro(std::hash<std::string>{}, "std::hash");
    double p_fnv = costo_puro(HashFNV{}, "FNV-1a");
    double p_pol = costo_puro(HashPolinomial{}, "polinomial p=31");
    double p_sum = costo_puro(HashSuma{}, "suma (malo)");
    std::cout << "   Ratio FNV-1a / std::hash: " << p_fnv / p_std << "x"
              << "   polinomial / std::hash: " << p_pol / p_std << "x"
              << "   suma / std::hash: " << p_sum / p_std << "x\n\n";

    // ---------- 3b. Benchmark con unordered_map ----------
    std::cout << "3b. BENCHMARK unordered_map (n = " << N
              << ", insertar + consultar todas las claves)\n";
    double ms_std = benchmarkHash<std::hash<std::string>>(claves, "std::hash", R);
    double ms_fnv = benchmarkHash<HashFNV>(claves, "FNV-1a", R);
    double ms_pol = benchmarkHash<HashPolinomial>(claves, "polinomial p=31", R);
    double ms_sum = benchmarkHash<HashSuma>(claves, "suma (malo)", R);
    std::cout << "\n   Ratio std::hash / FNV-1a     : " << ms_std / ms_fnv << "x\n";
    std::cout << "   Ratio polinomial / FNV-1a    : " << ms_pol / ms_fnv << "x\n";
    std::cout << "   Ratio suma (malo) / FNV-1a   : " << ms_sum / ms_fnv << "x\n\n";

    // ---------- 4. Efecto del factor de carga maximo ----------
    std::cout << "4. EFECTO DEL FACTOR DE CARGA MAXIMO (FNV-1a, n = " << N << ")\n";
    std::cout << "   " << std::setw(12) << std::left << "max_load" << std::right
              << std::setw(10) << "tiempo" << std::setw(10) << "celdas"
              << std::setw(10) << "carga\n";
    for (float lf : {0.25f, 0.5f, 1.0f, 2.0f, 4.0f}) {
        double ms = medir([&] {
            std::unordered_map<std::string, int, HashFNV> m;
            m.max_load_factor(lf);
            for (int i = 0; i < N; i++) m[claves[i]] = i;
            long long suma = 0;
            for (const auto& k : claves) suma += m[k];
            if (suma < 0) std::cout << "";
        }, R);
        std::unordered_map<std::string, int, HashFNV> m;
        m.max_load_factor(lf);
        for (int i = 0; i < N; i++) m[claves[i]] = i;
        std::cout << "   " << std::setw(12) << std::left << lf << std::right
                  << std::setw(8) << ms << " ms" << std::setw(10) << m.bucket_count()
                  << std::setw(10) << m.load_factor() << "\n";
    }

    // ---------- 5. El peor caso: claves que colisionan a proposito ----------
    // Con el hash por suma, los anagramas caen todos en la misma celda.
    std::cout << "\n5. ATAQUE POR COLISION (claves que son anagramas entre si)\n";
    std::vector<std::string> anagramas;
    std::string base = "abcdefgh";
    std::sort(base.begin(), base.end());
    do {
        anagramas.push_back(base);
        if (anagramas.size() >= 20000) break;
    } while (std::next_permutation(base.begin(), base.end()));
    std::cout << "   " << anagramas.size() << " permutaciones de \"abcdefgh\"\n";
    double ms_a_fnv = medir([&] {
        std::unordered_map<std::string, int, HashFNV> m;
        for (size_t i = 0; i < anagramas.size(); i++) m[anagramas[i]] = static_cast<int>(i);
    }, 3);
    double ms_a_sum = medir([&] {
        std::unordered_map<std::string, int, HashSuma> m;
        for (size_t i = 0; i < anagramas.size(); i++) m[anagramas[i]] = static_cast<int>(i);
    }, 3);
    std::cout << "   FNV-1a      : " << ms_a_fnv << " ms\n";
    std::cout << "   suma (malo) : " << ms_a_sum << " ms   -> "
              << ms_a_sum / ms_a_fnv << "x mas lento\n";
    std::cout << "   Con el hash por suma todas las claves caen en UNA celda y la\n";
    std::cout << "   tabla degenera en una lista enlazada: la busqueda pasa a O(n).\n";
    return 0;
}
