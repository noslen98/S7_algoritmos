# =============================================================
# Practica N.o 07 - Tablas Hash
# Curso: Algoritmos y Estructuras de Datos (SIS210) - UNAP Puno 2026
#
# Actividad 1: funciones hash y analisis de distribucion
# Actividad 2: TablaHashChaining (encadenamiento con listas enlazadas)
# Actividad 3: TablaHashOpenAddressing (sondeo lineal con DELETED)
# Actividad 4: miniestudio experimental del factor de carga
# Actividad 6: indice invertido
# Investigacion: hashing perfecto minimo (algoritmo BDZ)
#
# Ejecutar todo:           python3 Practica_S07_TablaHash_ApellidoNombre.py
# Una actividad concreta:  python3 Practica_S07_TablaHash_ApellidoNombre.py 4
# Preguntas de analisis:   python3 Practica_S07_TablaHash_ApellidoNombre.py preguntas
# Investigacion (MPH):     python3 Practica_S07_TablaHash_ApellidoNombre.py mph
# =============================================================
import sys
import re
import math
import time
import random
import string
import statistics
from collections import defaultdict
from dataclasses import dataclass
from typing import Optional, Any, Iterator


# =============================================================
# ACTIVIDAD 1 - Funciones hash y distribucion
# =============================================================
def hash_modulo(k: int, m: int) -> int:
    """Hash por modulo para claves enteras. O(1)."""
    return k % m


def hash_polinomial(s: str, m: int, p: int = 31) -> int:
    """Hash polinomial para cadenas - O(|s|).
    h(s) = (s[0]*p^0 + s[1]*p^1 + ... + s[n-1]*p^(n-1)) mod m"""
    h, potencia = 0, 1
    for c in s:
        h = (h + ord(c) * potencia) % m
        potencia = (potencia * p) % m
    return h


def hash_suma(s: str, m: int) -> int:
    """Hash INGENUO: suma los codigos de los caracteres.
    Se incluye como contraejemplo: ignora el orden, de modo que
    'amor', 'roma' y 'mora' caen todos en la misma celda."""
    return sum(ord(c) for c in s) % m


def medir_distribucion(claves, m, hash_fn) -> dict:
    """Cuenta cuantos elementos caen en cada celda y resume la dispersion."""
    tabla = [0] * m
    for k in claves:
        tabla[hash_fn(k, m)] += 1
    ocupadas = sum(1 for c in tabla if c > 0)
    promedio = len(claves) / m
    varianza = sum((c - promedio) ** 2 for c in tabla) / m
    cv = math.sqrt(varianza) / promedio if promedio > 0 else 0
    return {
        'ocupadas': ocupadas,
        'vacias': m - ocupadas,
        'max_colisiones': max(tabla),
        'cv': cv,
        'tabla': tabla,
    }


def cv_ideal(n: int, m: int) -> float:
    """CV teorico de un hash perfectamente uniforme.
    El reparto de n bolas en m urnas sigue una Binomial(n, 1/m), cuya
    desviacion tipica es sqrt(n*(1/m)*(1-1/m)); dividida entre la media
    n/m queda sqrt((1 - 1/m) * m / n)."""
    return math.sqrt((1 - 1 / m) * m / n)


# =============================================================
# ACTIVIDAD 2 - TablaHashChaining
# =============================================================
@dataclass
class Nodo:
    """Nodo de la Practica 5, ahora con un par (clave, valor)."""
    clave: Any
    valor: Any
    siguiente: 'Optional[Nodo]' = None


def siguiente_primo(n: int) -> int:
    """Primer primo mayor o igual que n."""
    def es_primo(x):
        return x > 1 and all(x % i for i in range(2, int(x ** 0.5) + 1))
    while not es_primo(n):
        n += 1
    return n


class TablaHashChaining:
    """Tabla hash con encadenamiento. Rehash automatico cuando alpha > 0.75."""

    UMBRAL = 0.75

    def __init__(self, m: int = 11, hash_fn=None):
        self._m = siguiente_primo(m)
        self._n = 0
        self._tabla: list = [None] * self._m     # cada celda es la cabeza de una lista
        self._rehashes = 0
        self._hash_fn = hash_fn or (lambda clave, m: hash(clave) % m)
        self._colisiones = 0                     # inserciones en una celda ya ocupada

    def _indice(self, clave) -> int:
        return self._hash_fn(clave, self._m)

    def insertar(self, clave, valor) -> None:
        idx = self._indice(clave)
        nodo = self._tabla[idx]
        while nodo is not None:                  # recorrer la cadena
            if nodo.clave == clave:
                nodo.valor = valor               # actualizar: no cambia el tamanio
                return
            nodo = nodo.siguiente
        if self._tabla[idx] is not None:
            self._colisiones += 1                # la celda ya estaba ocupada
        # insercion al inicio de la cadena: O(1)
        self._tabla[idx] = Nodo(clave, valor, self._tabla[idx])
        self._n += 1
        if self._n / self._m > self.UMBRAL:
            self._rehash()

    def buscar(self, clave):
        nodo = self._tabla[self._indice(clave)]
        while nodo is not None:
            if nodo.clave == clave:
                return nodo.valor
            nodo = nodo.siguiente
        return None

    def eliminar(self, clave) -> bool:
        idx = self._indice(clave)
        nodo, previo = self._tabla[idx], None
        while nodo is not None:
            if nodo.clave == clave:
                if previo is None:
                    self._tabla[idx] = nodo.siguiente   # era la cabeza
                else:
                    previo.siguiente = nodo.siguiente
                self._n -= 1
                return True
            previo, nodo = nodo, nodo.siguiente
        return False

    def _rehash(self) -> None:
        """Duplica el tamanio al siguiente primo y reinserta todo."""
        vieja = self._tabla
        self._m = siguiente_primo(self._m * 2)
        self._tabla = [None] * self._m
        self._n = 0
        self._rehashes += 1
        for cabeza in vieja:
            nodo = cabeza
            while nodo is not None:
                self.insertar(nodo.clave, nodo.valor)
                nodo = nodo.siguiente

    @property
    def factor_carga(self) -> float:
        return self._n / self._m

    @property
    def longitud_maxima(self) -> int:
        """Longitud de la cadena mas larga: el peor caso de una busqueda."""
        maxima = 0
        for cabeza in self._tabla:
            largo, nodo = 0, cabeza
            while nodo is not None:
                largo += 1
                nodo = nodo.siguiente
            maxima = max(maxima, largo)
        return maxima

    def __len__(self) -> int:
        return self._n

    def __contains__(self, clave) -> bool:
        return self.buscar(clave) is not None

    def __iter__(self) -> Iterator:
        for cabeza in self._tabla:
            nodo = cabeza
            while nodo is not None:
                yield nodo.clave, nodo.valor
                nodo = nodo.siguiente

    def __repr__(self) -> str:
        return (f'TablaHashChaining(m={self._m}, n={self._n}, '
                f'alpha={self.factor_carga:.2f}, rehashes={self._rehashes})')


# =============================================================
# ACTIVIDAD 3 - TablaHashOpenAddressing
# =============================================================
class TablaHashOpenAddressing:
    """Sondeo lineal con marcadores DELETED para una eliminacion correcta."""

    VACIA = object()       # centinela: celda nunca usada
    DELETED = object()     # centinela: celda liberada (no corta la cadena de sondeo)
    UMBRAL = 0.70

    def __init__(self, m: int = 11, hash_fn=None, usar_deleted: bool = True):
        self._m = siguiente_primo(m)
        self._n = 0                                  # elementos vivos
        self._ocupadas = 0                           # vivos + marcadas como DELETED
        self._tabla = [self.VACIA] * self._m
        self._rehashes = 0
        self._sondeos = 0                            # sondeos totales acumulados
        self._hash_fn = hash_fn or (lambda clave, m: hash(clave) % m)
        # usar_deleted=False reproduce el error que estudia la pregunta 10.1
        self._usar_deleted = usar_deleted

    def _indice(self, clave, j: int) -> int:
        """Sondeo lineal: h(k, j) = (h(k) + j) mod m."""
        return (self._hash_fn(clave, self._m) + j) % self._m

    def insertar(self, clave, valor) -> None:
        # El umbral se mide sobre las celdas OCUPADAS, no solo sobre las vivas:
        # los marcadores DELETED tambien alargan las cadenas de sondeo.
        if (self._ocupadas + 1) / self._m > self.UMBRAL:
            self._rehash()
        primer_hueco = None
        for j in range(self._m):
            idx = self._indice(clave, j)
            self._sondeos += 1
            celda = self._tabla[idx]
            if celda is self.VACIA:
                destino = primer_hueco if primer_hueco is not None else idx
                if destino == idx:
                    self._ocupadas += 1              # se estrena una celda
                self._tabla[destino] = (clave, valor)
                self._n += 1
                return
            if celda is self.DELETED:
                if primer_hueco is None:
                    primer_hueco = idx               # reutilizable si la clave no existe
            elif celda[0] == clave:
                self._tabla[idx] = (clave, valor)    # actualizar
                return
        raise RuntimeError('tabla llena: no hay ninguna celda libre')

    def buscar(self, clave):
        for j in range(self._m):
            idx = self._indice(clave, j)
            self._sondeos += 1
            celda = self._tabla[idx]
            if celda is self.VACIA:
                return None                          # cadena interrumpida -> no existe
            if celda is not self.DELETED and celda[0] == clave:
                return celda[1]
        return None

    def eliminar(self, clave) -> bool:
        for j in range(self._m):
            idx = self._indice(clave, j)
            celda = self._tabla[idx]
            if celda is self.VACIA:
                return False
            if celda is not self.DELETED and celda[0] == clave:
                # Usar VACIA aqui romperia la cadena de sondeo (vease la pregunta 10.1)
                self._tabla[idx] = self.DELETED if self._usar_deleted else self.VACIA
                if not self._usar_deleted:
                    self._ocupadas -= 1
                self._n -= 1
                return True
        return False

    def _rehash(self) -> None:
        """Reconstruye la tabla: duplica m y descarta los marcadores DELETED."""
        vieja = self._tabla
        self._m = siguiente_primo(self._m * 2)
        self._tabla = [self.VACIA] * self._m
        self._n = 0
        self._ocupadas = 0
        self._rehashes += 1
        for celda in vieja:
            if celda is not self.VACIA and celda is not self.DELETED:
                self.insertar(celda[0], celda[1])

    @property
    def factor_carga(self) -> float:
        return self._n / self._m

    @property
    def factor_ocupacion(self) -> float:
        """Incluye los marcadores DELETED: es el que determina el costo del sondeo."""
        return self._ocupadas / self._m

    @property
    def cluster_maximo(self) -> int:
        """Longitud del grupo contiguo de celdas ocupadas mas largo."""
        libres = [c is self.VACIA for c in self._tabla]
        if not any(libres):
            return self._m
        mayor = actual = 0
        # se recorre dos veces para contemplar un grupo que cruce el final
        for libre in libres + libres:
            actual = 0 if libre else actual + 1
            mayor = max(mayor, actual)
        return min(mayor, self._m)

    def __len__(self) -> int:
        return self._n

    def __contains__(self, clave) -> bool:
        return self.buscar(clave) is not None

    def __iter__(self) -> Iterator:
        for celda in self._tabla:
            if celda is not self.VACIA and celda is not self.DELETED:
                yield celda

    def mapa(self) -> str:
        """Dibuja la tabla: . vacia, X eliminada, letra inicial de la clave."""
        simbolos = []
        for celda in self._tabla:
            if celda is self.VACIA:
                simbolos.append('.')
            elif celda is self.DELETED:
                simbolos.append('X')
            else:
                simbolos.append(str(celda[0])[0])
        return ''.join(simbolos)

    def __repr__(self) -> str:
        return (f'TablaHashOpenAddressing(m={self._m}, n={self._n}, '
                f'alpha={self.factor_carga:.2f}, rehashes={self._rehashes})')


# =============================================================
# ACTIVIDAD 4 - Miniestudio experimental
# =============================================================
# Se usa el hash polinomial propio y no el hash() de Python porque este
# ultimo aleatoriza las cadenas en cada proceso (PYTHONHASHSEED), lo que
# haria irreproducible el miniestudio.


def claves_aleatorias(n: int, rng: random.Random, k: int = 8) -> list:
    """n cadenas distintas de k letras minusculas."""
    vistas = set()
    while len(vistas) < n:
        vistas.add(''.join(rng.choices(string.ascii_lowercase, k=k)))
    return list(vistas)


def medir_una_repeticion(claves: list, m: int) -> dict:
    """Inserta las claves en ambos esquemas y cuenta las colisiones.

    Encadenamiento: una colision es insertar en una celda ya ocupada.
    Sondeo lineal : una colision es cada sondeo adicional al primero.
    """
    tabla_ch = [0] * m
    col_ch = 0
    tabla_oa = [None] * m
    col_oa = 0
    ocupadas_oa = 0
    desbordada = False

    for k in claves:
        idx = hash_polinomial(k, m)

        # --- Encadenamiento: admite cualquier numero de elementos ---
        if tabla_ch[idx] > 0:
            col_ch += 1
        tabla_ch[idx] += 1

        # --- Sondeo lineal: no puede albergar mas de m elementos ---
        if ocupadas_oa >= m:
            desbordada = True            # la tabla esta llena: no se puede seguir
            continue
        j = 0
        while tabla_oa[(idx + j) % m] is not None:
            j += 1
            col_oa += 1
        tabla_oa[(idx + j) % m] = k
        ocupadas_oa += 1

    # longitud del grupo contiguo mas largo del sondeo lineal
    libres = [c is None for c in tabla_oa]
    if any(libres):
        mayor = actual = 0
        for libre in libres + libres:
            actual = 0 if libre else actual + 1
            mayor = max(mayor, actual)
        cluster = min(mayor, m)
    else:
        cluster = m

    return {
        'col_ch': col_ch,
        'col_oa': col_oa,
        'cadena_max': max(tabla_ch),
        'cluster_max': cluster,
        'desbordada': desbordada,
        'insertadas_oa': ocupadas_oa,
    }


def medir_colisiones_reales(n_elementos: int, m_tabla: int, n_rep: int = 10,
                            semilla: int = 7) -> dict:
    """Promedia n_rep repeticiones independientes."""
    rng = random.Random(semilla)
    acum = {'col_ch': [], 'col_oa': [], 'cadena_max': [], 'cluster_max': []}
    desbordada = False
    insertadas_oa = n_elementos
    for _ in range(n_rep):
        r = medir_una_repeticion(claves_aleatorias(n_elementos, rng), m_tabla)
        for clave in acum:
            acum[clave].append(r[clave])
        desbordada = desbordada or r['desbordada']
        insertadas_oa = r['insertadas_oa']
    return {
        'col_ch': statistics.mean(acum['col_ch']),
        'col_oa': statistics.mean(acum['col_oa']),
        'cadena_max': statistics.mean(acum['cadena_max']),
        'cluster_max': statistics.mean(acum['cluster_max']),
        'desbordada': desbordada,
        'insertadas_oa': insertadas_oa,
    }


# Comparaciones esperadas por la teoria (Cormen et al., 2022, cap. 11)
def esperado_chaining(alpha: float) -> float:
    """Busqueda con exito: 1 + alpha/2."""
    return 1 + alpha / 2


def esperado_lineal(alpha: float) -> float:
    """Busqueda con exito en sondeo lineal: (1 + 1/(1-alpha)) / 2."""
    if alpha >= 1:
        return float('inf')
    return 0.5 * (1 + 1 / (1 - alpha))


# =============================================================
# ACTIVIDAD 6 - Indice invertido
# =============================================================
# Catalogo simulado de la Biblioteca Central UNA-PUNO
DOCUMENTOS = {
    1: 'Algoritmos y estructuras de datos en Python para ingenieria',
    2: 'Analisis de complejidad computacional y algoritmos recursivos',
    3: 'Estructuras de datos lineales: listas pilas y colas',
    4: 'Tablas hash y funciones de dispersion para bases de datos',
    5: 'Arboles binarios de busqueda y algoritmos de recorrido',
    6: 'Grafos y algoritmos de caminos minimos en redes viales',
    7: 'Fundamentos de programacion en C++ para sistemas embebidos',
    8: 'Estructuras de datos avanzadas: tablas hash y arboles balanceados',
    9: 'Complejidad de algoritmos de ordenamiento y busqueda',
    10: 'Redes de computadoras y protocolos de comunicacion de datos',
}

STOP_WORDS = {'y', 'de', 'en', 'para', 'el', 'la', 'los', 'las',
              'a', 'e', 'o', 'un', 'una', 'con', 'del', 'al'}

def normalizar(titulo: str) -> list:
    """Separa en palabras, pasa a minusculas y descarta signos y vacios."""
    limpio = ''.join(c if c.isalnum() or c in '+ ' else ' ' for c in titulo.lower())
    return [p for p in limpio.split() if p not in STOP_WORDS and len(p) > 2]

def construir_indice_invertido(docs: dict) -> dict:
    """Construye un indice invertido {palabra: {doc_id, ...}}.
    Complejidad O(N), con N el numero total de palabras de todos los documentos:
    cada palabra se inserta en la tabla hash en O(1) promedio."""
    indice = defaultdict(set)
    for doc_id, titulo in docs.items():
        for palabra in normalizar(titulo):
            indice[palabra].add(doc_id)
    return dict(indice)

def buscar_and(indice: dict, consulta: str) -> list:
    """Busqueda multi-termino: interseccion (todos los terminos)."""
    palabras = normalizar(consulta)
    if not palabras:
        return []
    # Empezar por el termino menos frecuente acota la interseccion cuanto antes
    palabras.sort(key=lambda p: len(indice.get(p, ())))
    resultados = set(indice.get(palabras[0], set()))
    for p in palabras[1:]:
        resultados &= indice.get(p, set())
        if not resultados:
            break                       # interseccion vacia: no hace falta seguir
    return sorted(resultados)

def buscar_or(indice: dict, consulta: str) -> list:
    """Busqueda multi-termino: union (al menos un termino)."""
    palabras = normalizar(consulta)
    resultados = set()
    for p in palabras:
        resultados |= indice.get(p, set())
    return sorted(resultados)

def documentos_por_relevancia(indice: dict, consulta: str) -> list:
    """Ordena por cuantos terminos de la consulta aparecen en cada documento."""
    palabras = normalizar(consulta)
    puntajes = defaultdict(int)
    for p in palabras:
        for doc_id in indice.get(p, set()):
            puntajes[doc_id] += 1
    return sorted(puntajes.items(), key=lambda par: (-par[1], par[0]))


# =============================================================
# INVESTIGACION - Hashing perfecto minimo (BDZ)
# =============================================================
def _hash(clave: str, semilla: int, i: int) -> int:
    """Familia de hashes independientes: FNV-1a con la semilla mezclada."""
    h = 14695981039346656037 ^ (semilla * 0x9E3779B97F4A7C15) ^ (i * 0x100000001B3)
    h &= 0xFFFFFFFFFFFFFFFF
    for c in clave:
        h ^= ord(c)
        h = (h * 1099511628211) & 0xFFFFFFFFFFFFFFFF
    h ^= h >> 33                       # mezcla final: mejora la avalancha
    h = (h * 0xFF51AFD7ED558CCD) & 0xFFFFFFFFFFFFFFFF
    h ^= h >> 33
    return h


class HashPerfectoMinimo:
    """Funcion hash perfecta minima: n claves -> [0, n-1] sin colisiones.

    Construccion en tres fases (BDZ):
      1. Mapeo    : cada clave define una arista de un hipergrafo 3-partito.
      2. Peeling  : se retiran aristas con un vertice de grado 1; si se
                    retiran todas, el hipergrafo es aciclico y hay solucion.
      3. Asignacion: recorriendo el orden inverso se fija g[v] in {0,1,2}
                    de modo que cada clave reclame un vertice distinto.
      4. Ranking  : se comprime el rango [0, m-1] a [0, n-1].
    """

    def __init__(self, claves, c: float = 1.23, max_intentos: int = 20,
                 semilla: int = 0):
        self._n = len(claves)
        if self._n == 0:
            self._m = self._particion = 0
            self._g, self._rango, self._semilla, self._intentos = [], [], 0, 0
            return
        m = max(3, math.ceil(c * self._n))
        m += (3 - m % 3) % 3                       # m multiplo de 3
        self._m = m
        self._particion = m // 3

        for intento in range(max_intentos):
            s = semilla + intento
            aristas = [self._arista(k, s) for k in claves]
            pila = self._peel(aristas)
            if pila is not None:                   # hipergrafo aciclico
                self._semilla = s
                self._intentos = intento + 1
                self._asignar(aristas, pila)
                return
        raise RuntimeError(f'no se obtuvo un hipergrafo aciclico en '
                           f'{max_intentos} intentos (pruebe un c mayor)')

    # --- Fase 1: mapeo ---
    def _arista(self, clave, s: int) -> tuple:
        p = self._particion
        return (_hash(clave, s, 0) % p,
                p + _hash(clave, s, 1) % p,
                2 * p + _hash(clave, s, 2) % p)

    # --- Fase 2: peeling ---
    def _peel(self, aristas):
        """Retira aristas con algun vertice de grado 1.
        Devuelve el orden de retirada, o None si quedan aristas (hay ciclos)."""
        incidencia = [[] for _ in range(self._m)]
        for i, e in enumerate(aristas):
            for v in e:
                incidencia[v].append(i)
        grado = [len(inc) for inc in incidencia]
        viva = [True] * len(aristas)
        pila = []
        cola = [v for v in range(self._m) if grado[v] == 1]
        while cola:
            v = cola.pop()
            if grado[v] != 1:
                continue
            arista = next((i for i in incidencia[v] if viva[i]), None)
            if arista is None:
                continue
            viva[arista] = False
            e = aristas[arista]
            pila.append((arista, e.index(v)))      # (arista, posicion del unico)
            for u in e:
                grado[u] -= 1
                if grado[u] == 1:
                    cola.append(u)
        return pila if len(pila) == len(aristas) else None

    # --- Fases 3 y 4: asignacion y ranking ---
    def _asignar(self, aristas, pila):
        g = [0] * self._m                 # sin asignar se interpreta como 0
        asignado = [False] * self._m
        for arista, j in reversed(pila):  # orden inverso al del peeling
            e = aristas[arista]
            otros = g[e[(j + 1) % 3]] + g[e[(j + 2) % 3]]
            g[e[j]] = (j - otros) % 3     # el unico vertice reclama la arista
            asignado[e[j]] = True
        self._g = g
        # rango[v] = cuantos vertices asignados hay antes de v  -> comprime a [0, n)
        rango, acumulado = [0] * self._m, 0
        for v in range(self._m):
            rango[v] = acumulado
            if asignado[v]:
                acumulado += 1
        self._rango = rango
        assert acumulado == self._n

    # --- Consulta ---
    def __call__(self, clave) -> int:
        e = self._arista(clave, self._semilla)
        return self._rango[e[(self._g[e[0]] + self._g[e[1]] + self._g[e[2]]) % 3]]

    @property
    def bits_por_clave(self) -> float:
        """Tamanio de la estructura: g usa 2 bits por vertice.
        El rango se puede almacenar en o(n) bits con una estructura de rank
        sucinta; aqui se contabiliza solo la cota teorica de g."""
        return 2 * self._m / self._n

    def __len__(self) -> int:
        return self._n

    def __repr__(self) -> str:
        return (f'HashPerfectoMinimo(n={self._n}, m={self._m}, '
                f'c={self._m / self._n:.2f}, intentos={self._intentos}, '
                f'{self.bits_por_clave:.2f} bits/clave)')


def claves_mph(n, rng, k=12):
    """Claves de prueba para el MPH (nombre propio: actividad4 define otra)."""
    vistas = set()
    while len(vistas) < n:
        vistas.add(''.join(rng.choices(string.ascii_lowercase, k=k)))
    return list(vistas)


# =============================================================
# PREGUNTAS DE ANALISIS
# =============================================================
# =============================================================
# PREGUNTA 1 - Por que DELETED y no VACIA
# =============================================================
# Hash controlado: fuerza las colisiones del ejemplo para que sea reproducible.
POSICIONES = {'Puno': 3, 'Pisco': 3, 'Pucallpa': 3, 'Tacna': 5, 'Ica': 0}


def hash_controlado(clave, m):
    return POSICIONES.get(clave, hash_polinomial(str(clave), m)) % m


def demo_deleted(usar_deleted: bool) -> dict:
    """Las 5 inserciones del ejemplo, eliminando despues 'Pisco'."""
    t = TablaHashOpenAddressing(m=7, hash_fn=hash_controlado,
                                usar_deleted=usar_deleted)
    t.UMBRAL = 1.0          # sin rehash: el ejemplo debe quedarse en m = 7
    orden = ['Puno', 'Pisco', 'Pucallpa', 'Tacna', 'Ica']
    for i, clave in enumerate(orden):
        t.insertar(clave, i)
    mapa_antes = t.mapa()
    t.eliminar('Pisco')
    return {
        'antes': mapa_antes,
        'despues': t.mapa(),
        'resultados': {c: t.buscar(c) for c in orden},
    }


def pregunta1():
    print('=' * 68)
    print('PREGUNTA 1: por que DELETED y no VACIA al eliminar')
    print('=' * 68)
    print('Tabla de m = 7 celdas. Hash controlado para forzar el agrupamiento:')
    for clave, pos in POSICIONES.items():
        print(f'   h({clave!r:11}) = {pos}')

    print('\nLas 5 inserciones, en orden:')
    traza = [('Puno', 3, 3, 'celda 3 libre'),
             ('Pisco', 3, 4, 'celda 3 ocupada por Puno -> sondeo j=1'),
             ('Pucallpa', 3, 5, 'celdas 3 y 4 ocupadas -> sondeo j=2'),
             ('Tacna', 5, 6, 'celda 5 ocupada por Pucallpa -> sondeo j=1'),
             ('Ica', 0, 0, 'celda 0 libre')]
    for clave, h, destino, motivo in traza:
        print(f'   {clave:10} h={h}  ->  celda {destino}   ({motivo})')

    con = demo_deleted(usar_deleted=True)
    sin = demo_deleted(usar_deleted=False)

    print(f'\nEstado de la tabla (celdas 0..6):')
    print(f'   tras las 5 inserciones : {con["antes"]}')
    print(f'   tras eliminar Pisco, con DELETED : {con["despues"]}   '
          f'(X = marcador DELETED)')
    print(f'   tras eliminar Pisco, con VACIA   : {sin["despues"]}   '
          f'(. = celda vacia)')

    print(f'\nBusquedas despues de eliminar Pisco:')
    print(f'   {"clave":10} {"con DELETED":>13} {"con VACIA":>12}   {"":2}')
    fallos = 0
    for clave in ['Puno', 'Pisco', 'Pucallpa', 'Tacna', 'Ica']:
        a, b = con['resultados'][clave], sin['resultados'][clave]
        marca = ''
        if a != b:
            marca = '<- FALSO NEGATIVO'
            fallos += 1
        print(f'   {clave:10} {str(a):>13} {str(b):>12}   {marca}')

    print(f'\nCon VACIA se pierden {fallos} clave(s) que SIGUEN en la tabla.')
    print('Buscar Pucallpa sondea 3 (Puno, no coincide), luego 4: con VACIA el')
    print('algoritmo concluye que la cadena termino y devuelve None, aunque')
    print('Pucallpa esta en la celda 5.')
    assert fallos == 1 and sin['resultados']['Pucallpa'] is None
    assert con['resultados']['Pucallpa'] == 2
    print('Verificado: DELETED preserva la cadena de sondeo, VACIA la rompe.')


# =============================================================
# PREGUNTA 2 - Clustering primario y sondeo cuadratico
# =============================================================
def insertar_sondeo(claves, m, modo):
    """Inserta las claves con el sondeo indicado y devuelve sondeos y clusters."""
    tabla = [None] * m
    sondeos = 0
    for k in claves:
        h = hash_polinomial(k, m)
        for j in range(m):
            if modo == 'lineal':
                idx = (h + j) % m
            elif modo == 'cuadratico':
                idx = (h + j * j) % m
            else:                                     # doble hash
                paso = 1 + hash_polinomial(k, m - 1, p=37)
                idx = (h + j * paso) % m
            sondeos += 1
            if tabla[idx] is None:
                tabla[idx] = k
                break
        else:
            return None                               # no encontro hueco
    libres = [c is None for c in tabla]
    if any(libres):
        mayor = actual = 0
        for libre in libres + libres:
            actual = 0 if libre else actual + 1
            mayor = max(mayor, actual)
        cluster = min(mayor, m)
    else:
        cluster = m
    return {'sondeos': sondeos / len(claves), 'cluster': cluster}


def pregunta2():
    print('\n' + '=' * 68)
    print('PREGUNTA 2: clustering primario y sondeo cuadratico')
    print('=' * 68)
    m = 1009
    rng = random.Random(11)
    print(f'Tabla de m = {m} celdas, 5 repeticiones por configuracion\n')
    print(f'{"alpha":>6} | {"LINEAL":^20} | {"CUADRATICO":^20} | {"DOBLE HASH":^20}')
    print(f'{"":>6} | {"sondeos":>9} {"cluster":>10} | {"sondeos":>9} {"cluster":>10} '
          f'| {"sondeos":>9} {"cluster":>10}')
    filas = []
    for alpha in [0.25, 0.50, 0.75, 0.85, 0.90, 0.95]:
        n = int(alpha * m)
        acum = {modo: {'sondeos': [], 'cluster': []} for modo in
                ('lineal', 'cuadratico', 'doble')}
        for _ in range(5):
            claves = []
            vistas = set()
            while len(vistas) < n:
                c = ''.join(rng.choices(string.ascii_lowercase, k=8))
                if c not in vistas:
                    vistas.add(c)
                    claves.append(c)
            for modo in acum:
                r = insertar_sondeo(claves, m, modo)
                if r:
                    acum[modo]['sondeos'].append(r['sondeos'])
                    acum[modo]['cluster'].append(r['cluster'])
        def prom(modo, campo):
            v = acum[modo][campo]
            return statistics.mean(v) if v else float('nan')
        filas.append((alpha, {modo: (prom(modo, 'sondeos'), prom(modo, 'cluster'))
                              for modo in acum}))
        print(f'{alpha:>6.2f} | '
              f'{prom("lineal", "sondeos"):>9.2f} {prom("lineal", "cluster"):>10.1f} | '
              f'{prom("cuadratico", "sondeos"):>9.2f} '
              f'{prom("cuadratico", "cluster"):>10.1f} | '
              f'{prom("doble", "sondeos"):>9.2f} {prom("doble", "cluster"):>10.1f}')

    a, datos = filas[-1]
    print(f'\nEn alpha = {a:.2f} el sondeo lineal necesita '
          f'{datos["lineal"][0] / datos["cuadratico"][0]:.1f} veces mas sondeos')
    print(f'que el cuadratico, y su grupo contiguo mas largo es '
          f'{datos["lineal"][1] / datos["cuadratico"][1]:.1f} veces mayor.')
    return filas


# =============================================================
# PREGUNTA 3 - Complejidad del indice invertido
# =============================================================
def pregunta3():
    print('\n' + '=' * 68)
    print('PREGUNTA 3: complejidad de buscar() en el indice invertido')
    print('=' * 68)
    rng = random.Random(3)
    # Corpus con frecuencias tipo Zipf, como en el lenguaje real: unos pocos
    # terminos aparecen en casi todos los documentos y la mayoria en muy pocos.
    terminos = [f't{i}' for i in range(2000)]
    pesos = [1.0 / (i + 1) for i in range(len(terminos))]
    corpus = {}
    for doc in range(8000):
        corpus[doc] = ' '.join(rng.choices(terminos, weights=pesos, k=15))
    indice = construir_indice_invertido(corpus)
    tam = {p: len(v) for p, v in indice.items()}
    print(f'Corpus: {len(corpus):,} documentos, {len(indice)} terminos')
    print(f'Documentos por termino: minimo={min(tam.values())}, '
          f'maximo={max(tam.values())}, mediana={statistics.median(tam.values()):.0f}')

    def cronometrar(fn, indice, q, rep=200):
        fn(indice, q)                                  # calentamiento
        t0 = time.perf_counter()
        for _ in range(rep):
            fn(indice, q)
        return (time.perf_counter() - t0) * 1e6 / rep  # microsegundos

    print(f'\n--- Efecto de q (numero de terminos de la consulta) ---')
    print(f'{"q":>3} {"AND (us)":>10} {"OR (us)":>10} {"|AND|":>7} {"|OR|":>7}')
    for q in [1, 2, 3, 4, 6, 8]:
        consulta = ' '.join(rng.sample(terminos, q))
        t_and = cronometrar(buscar_and, indice, consulta)
        t_or = cronometrar(buscar_or, indice, consulta)
        print(f'{q:>3} {t_and:>10.1f} {t_or:>10.1f} '
              f'{len(buscar_and(indice, consulta)):>7} '
              f'{len(buscar_or(indice, consulta)):>7}')

    print(f'\n--- Efecto de k (documentos por termino) con q = 2 ---')
    print(f'{"k1":>7} {"k2":>7} {"AND (us)":>10} {"OR (us)":>10} {"|OR|":>7}')
    por_tam = sorted(indice.items(), key=lambda x: len(x[1]))
    for frac in [0.10, 0.50, 0.90, 0.99, 1.0]:
        i = min(int(frac * (len(por_tam) - 1)), len(por_tam) - 2)
        p1, docs1 = por_tam[i]
        p2, docs2 = por_tam[i + 1]
        consulta = f'{p1} {p2}'
        print(f'{len(docs1):>7} {len(docs2):>7} '
              f'{cronometrar(buscar_and, indice, consulta):>10.1f} '
              f'{cronometrar(buscar_or, indice, consulta):>10.1f} '
              f'{len(buscar_or(indice, consulta)):>7}')

    print('\n--- Ventaja de empezar por el termino menos frecuente (AND) ---')
    def and_sin_ordenar(indice, consulta):
        palabras = normalizar(consulta)
        if not palabras:
            return []
        res = set(indice.get(palabras[0], set()))
        for p in palabras[1:]:
            res &= indice.get(p, set())
        return sorted(res)

    raro = min(indice, key=lambda p: len(indice[p]))
    comun = max(indice, key=lambda p: len(indice[p]))
    print(f'   termino raro  : {raro!r} en {len(indice[raro])} documentos')
    print(f'   termino comun : {comun!r} en {len(indice[comun])} documentos')
    for etiqueta, consulta in [('comun primero', f'{comun} {raro}'),
                               ('raro primero ', f'{raro} {comun}')]:
        t_opt = cronometrar(buscar_and, indice, consulta)
        t_nai = cronometrar(and_sin_ordenar, indice, consulta)
        print(f'   {etiqueta}: con ordenacion {t_opt:7.1f} us, '
              f'sin ordenacion {t_nai:7.1f} us')


# =============================================================
# PREGUNTA 4 - Como preserva el orden el dict de Python
# =============================================================
def pregunta4():
    print('\n' + '=' * 68)
    print('PREGUNTA 4: como preserva el dict el orden sin perder el O(1)')
    print('=' * 68)
    print(f'Python {sys.version.split()[0]}\n')

    print('--- El orden de insercion se conserva ---')
    d = {}
    for clave in ['zeta', 'alfa', 'mu', 'beta', 'omega']:
        d[clave] = len(clave)
    print(f'   insercion : zeta, alfa, mu, beta, omega')
    print(f'   recorrido : {", ".join(d)}')
    assert list(d) == ['zeta', 'alfa', 'mu', 'beta', 'omega']

    print('\n--- Pero NO esta ordenado por clave ni por hash ---')
    print(f'   ordenado por clave seria : {", ".join(sorted(d))}')
    print('   el dict NO los devuelve asi, luego no es una estructura ordenada')

    print('\n--- Eliminar e insertar: el nuevo va al final, no al hueco ---')
    del d['alfa']
    d['alfa'] = 4
    print(f'   tras borrar e insertar "alfa" : {", ".join(d)}')
    assert list(d)[-1] == 'alfa'

    print('\n--- El acceso sigue siendo O(1): tiempo por consulta ---')
    print(f'{"n":>10} {"ns por consulta":>17}')
    for n in [1000, 10000, 100000, 1000000]:
        grande = {f'clave{i}': i for i in range(n)}
        muestras = [f'clave{random.randrange(n)}' for _ in range(1000)]
        for k in muestras[:100]:
            _ = grande[k]
        t0 = time.perf_counter_ns()
        for _ in range(20):
            for k in muestras:
                _ = grande[k]
        ns = (time.perf_counter_ns() - t0) / (20 * len(muestras))
        print(f'{n:>10,} {ns:>17.1f}')
    print('   El tiempo no crece con n: el acceso sigue siendo O(1).')

    print('\n--- La clave: dos arreglos en lugar de uno (dict compacto) ---')
    print('   El diseno antiguo guardaba una tabla dispersa de entradas completas')
    print('   (hash, clave, valor) con huecos. El diseno compacto separa:')
    print('     indices[]  : tabla dispersa y pequena, solo enteros -> posicion')
    print('     entradas[] : arreglo DENSO y en orden de insercion')
    print('   El hash localiza una posicion en indices[], que apunta a entradas[].')
    print('   Recorrer el dict es recorrer entradas[] en orden: por eso el orden')
    print('   se conserva sin coste adicional, y la busqueda sigue siendo O(1).')

    print('\n--- Consecuencia medible: el dict compacto ocupa menos memoria ---')
    print(f'{"n":>8} {"bytes":>12} {"bytes/clave":>13}')
    for n in [8, 64, 512, 4096, 32768]:
        d2 = {i: i for i in range(n)}
        print(f'{n:>8} {sys.getsizeof(d2):>12,} {sys.getsizeof(d2) / n:>13.1f}')
    print('   Con el diseno antiguo cada entrada ocupaba 24 bytes en una tabla')
    print('   dispersa con 1/3 de huecos; el compacto solo desperdicia enteros.')

    print('\n--- Comprobacion: dict frente a OrderedDict ---')
    from collections import OrderedDict
    n = 100000
    t0 = time.perf_counter()
    d3 = {i: i for i in range(n)}
    t_dict = (time.perf_counter() - t0) * 1000
    t0 = time.perf_counter()
    od = OrderedDict((i, i) for i in range(n))
    t_od = (time.perf_counter() - t0) * 1000
    print(f'   dict        : {t_dict:7.2f} ms, {sys.getsizeof(d3):>10,} bytes')
    print(f'   OrderedDict : {t_od:7.2f} ms, {sys.getsizeof(od):>10,} bytes')
    print(f'   OrderedDict usa {sys.getsizeof(od) / sys.getsizeof(d3):.1f} veces mas')
    print('   memoria porque anade una lista doblemente enlazada para el orden;')
    print('   el dict lo consigue gratis con su arreglo denso.')


# =============================================================
# DEMOSTRACIONES
# =============================================================
def _titulo(t):
    print('\n' + '=' * 62)
    print(t)
    print('=' * 62)


def actividad1():
    _titulo('ACTIVIDAD 1 - Funciones hash y distribucion')
    random.seed(42)                      # resultados reproducibles
    m = 101                              # primo
    n = 500

    print(f'Parametros: m = {m} (primo), n = {n}, '
          f'factor de carga = {n / m:.2f}\n')

    # --- Hash de enteros ---
    claves_int = [random.randint(0, 1_000_000) for _ in range(n)]
    s_int = medir_distribucion(claves_int, m, hash_modulo)
    print(f'Hash enteros   (modulo)     : celdas_ocupadas={s_int["ocupadas"]:>3}/{m}, '
          f'max_col={s_int["max_colisiones"]:>2}, CV={s_int["cv"]:.3f}')

    # --- Hash de cadenas ---
    claves_str = [''.join(random.choices(string.ascii_lowercase, k=8))
                  for _ in range(n)]
    s_str = medir_distribucion(claves_str, m, hash_polinomial)
    print(f'Hash cadenas   (polinomial) : celdas_ocupadas={s_str["ocupadas"]:>3}/{m}, '
          f'max_col={s_str["max_colisiones"]:>2}, CV={s_str["cv"]:.3f}')

    # --- Contraejemplo: el hash por suma ---
    s_sum = medir_distribucion(claves_str, m, hash_suma)
    print(f'Hash cadenas   (suma, malo) : celdas_ocupadas={s_sum["ocupadas"]:>3}/{m}, '
          f'max_col={s_sum["max_colisiones"]:>2}, CV={s_sum["cv"]:.3f}')

    print(f'\nCV de referencia de un hash uniforme ideal: {cv_ideal(n, m):.3f}')
    print('(CV cercano a ese valor -> distribucion uniforme; CV mayor -> agrupamiento)')

    # --- Por que m debe ser primo ---
    print('\n--- Efecto de elegir m primo o compuesto (claves multiplos de 4) ---')
    claves_sesgadas = [4 * i for i in range(n)]
    for mm, etiqueta in [(101, 'primo'), (100, 'compuesto'), (128, 'potencia de 2')]:
        s = medir_distribucion(claves_sesgadas, mm, hash_modulo)
        print(f'  m = {mm:>3} ({etiqueta:14}): ocupadas={s["ocupadas"]:>3}/{mm}, '
              f'max_col={s["max_colisiones"]:>2}, CV={s["cv"]:.3f}')
    print('  Con m compuesto, las claves multiplos de 4 solo alcanzan las celdas')
    print('  multiplos de gcd(4, m), y el resto de la tabla queda desierto.')

    # --- La propiedad de avalancha ---
    print('\n--- Avalancha: cambiar una letra debe cambiar el indice ---')
    base = 'algoritmo'
    print(f'  {"clave":12} {"polinomial":>11} {"suma":>6}')
    for palabra in [base, 'algoritmp', 'blgoritmo', 'algoritmos']:
        print(f'  {palabra:12} {hash_polinomial(palabra, m):>11} '
              f'{hash_suma(palabra, m):>6}')

    # --- Anagramas: el punto debil del hash por suma ---
    print('\n--- Anagramas (mismo multiconjunto de letras) ---')
    print(f'  {"clave":8} {"polinomial":>11} {"suma":>6}')
    for palabra in ['amor', 'roma', 'mora', 'ramo', 'omar']:
        print(f'  {palabra:8} {hash_polinomial(palabra, m):>11} '
              f'{hash_suma(palabra, m):>6}')
    indices_suma = {hash_suma(w, m) for w in ['amor', 'roma', 'mora', 'ramo', 'omar']}
    indices_pol = {hash_polinomial(w, m) for w in ['amor', 'roma', 'mora', 'ramo', 'omar']}
    print(f'  Celdas distintas -> polinomial: {len(indices_pol)}/5, '
          f'suma: {len(indices_suma)}/5')
    assert len(indices_suma) == 1, 'el hash por suma deberia colisionar en los anagramas'
    print('  El hash por suma envia los 5 anagramas a la MISMA celda.')

def actividad2():
    _titulo('ACTIVIDAD 2 - TablaHashChaining')
    # --- Prueba de la guia: altitudes de ciudades ---
    t = TablaHashChaining(m=7)
    ciudades = [('Puno', 3825), ('Juliaca', 3825), ('Arequipa', 2335), ('Lima', 154),
                ('Cusco', 3400), ('Iquitos', 106), ('Trujillo', 34), ('Huancayo', 3271)]
    for ciudad, alt in ciudades:
        t.insertar(ciudad, alt)
    print(f'Tras insertar {len(ciudades)} ciudades: {t}')
    assert t.buscar('Puno') == 3825
    assert t.eliminar('Lima')
    assert t.buscar('Lima') is None
    assert not t.eliminar('Lima')          # ya no esta
    print('TablaHashChaining: OK')

    # --- El rehashing mantiene el factor de carga bajo control ---
    print('\n--- Evolucion del rehashing al insertar 200 claves ---')
    t2 = TablaHashChaining(m=7)
    print(f'  {"insertadas":>10} {"m":>6} {"alpha":>7} {"rehashes":>9} {"cadena max":>11}')
    for i in range(1, 201):
        t2.insertar(f'clave{i}', i)
        if i in (5, 10, 25, 50, 100, 150, 200):
            print(f'  {i:>10} {t2._m:>6} {t2.factor_carga:>7.2f} '
                  f'{t2._rehashes:>9} {t2.longitud_maxima:>11}')
    assert t2.factor_carga <= TablaHashChaining.UMBRAL
    assert len(t2) == 200
    print(f'  El factor de carga nunca supera el umbral de {TablaHashChaining.UMBRAL}')

    # --- Todas las claves siguen accesibles tras los rehashes ---
    assert all(t2.buscar(f'clave{i}') == i for i in range(1, 201))
    print('  Las 200 claves siguen siendo recuperables tras los rehashes: OK')

    # --- Actualizar no duplica ---
    t3 = TablaHashChaining(m=11)
    t3.insertar('a', 1)
    t3.insertar('a', 2)
    assert len(t3) == 1 and t3.buscar('a') == 2
    print('  Reinsertar una clave existente actualiza y no duplica: OK')

def actividad3():
    _titulo('ACTIVIDAD 3 - TablaHashOpenAddressing')
    ciudades = [('Puno', 3825), ('Juliaca', 3825), ('Arequipa', 2335), ('Lima', 154),
                ('Cusco', 3400), ('Iquitos', 106), ('Trujillo', 34), ('Huancayo', 3271)]

    # --- Prueba de la guia ---
    t2 = TablaHashOpenAddressing(m=13)
    for ciudad, alt in ciudades:
        t2.insertar(ciudad, alt)
    assert t2.buscar('Puno') == 3825
    t2.eliminar('Juliaca')
    assert t2.buscar('Juliaca') is None
    assert t2.buscar('Puno') == 3825        # la cadena no se rompio gracias al DELETED
    print(f'Tras insertar 8 ciudades y eliminar una: {t2}')
    print('TablaHashOpenAddressing: OK')

    # --- El umbral tambien cuenta los marcadores DELETED ---
    print('\n--- Insertar y eliminar 500 veces sobre una tabla pequena ---')
    t3 = TablaHashOpenAddressing(m=11)
    for i in range(500):
        t3.insertar(f'k{i}', i)
        if i % 2 == 0:
            t3.eliminar(f'k{i}')
    print(f'  {t3}')
    print(f'  vivos={len(t3)}, ocupacion real={t3.factor_ocupacion:.2f}, '
          f'cluster maximo={t3.cluster_maximo}')
    assert all(t3.buscar(f'k{i}') == i for i in range(1, 500, 2))
    assert all(t3.buscar(f'k{i}') is None for i in range(0, 500, 2))
    print('  Las 250 claves vivas se encuentran y las 250 eliminadas no: OK')

    # --- El rehash descarta los marcadores ---
    antes = t3.factor_ocupacion
    t3._rehash()
    print(f'  Ocupacion antes del rehash: {antes:.2f} -> despues: '
          f'{t3.factor_ocupacion:.2f}  (los DELETED desaparecen)')
    assert all(t3.buscar(f'k{i}') == i for i in range(1, 500, 2))
    print('  Las claves vivas sobreviven al rehash: OK')

def actividad4():
    _titulo('ACTIVIDAD 4 - Miniestudio experimental')
    M = 1009                               # primo cercano a 1000
    N_REP = 10
    configs = [(252, M), (504, M), (756, M), (1009, M), (1513, M), (2018, M)]

    print(f'Miniestudio: m = {M} (primo), {N_REP} repeticiones por configuracion')
    print(f'Hash: polinomial propio con p = 31 (reproducible)\n')
    print(f'{"alpha":>7} {"n":>6} {"m":>6} {"Col.Chain":>11} {"Col.OpenAddr":>14} '
          f'{"%Col/n":>8} {"cadena":>7} {"cluster":>8}')

    filas = []
    for n, m in configs:
        r = medir_colisiones_reales(n, m, N_REP)
        alpha = n / m
        col_oa = 'no aplica' if r['desbordada'] else f'{r["col_oa"]:.1f}'
        print(f'{alpha:>7.2f} {n:>6} {m:>6} {r["col_ch"]:>11.1f} {col_oa:>14} '
              f'{r["col_ch"] / n * 100:>7.1f}% {r["cadena_max"]:>7.1f} '
              f'{r["cluster_max"]:>8.1f}')
        filas.append((alpha, n, m, r))

    print('\n"no aplica" significa que el sondeo lineal NO PUEDE almacenar mas de m')
    print('elementos: con alpha > 1 la tabla se llena y el bucle de sondeo no termina.')
    print('Por eso la teoria indica un costo infinito para el sondeo lineal en alpha = 1.')

    # --- Comparaciones por busqueda: medido frente a teoria ---
    print('\n--- Sondeos por insercion: medido frente a la prediccion teorica ---')
    print(f'{"alpha":>7} {"chain medido":>13} {"chain teorico":>14} '
          f'{"lineal medido":>14} {"lineal teorico":>15}')
    for alpha, n, m, r in filas:
        ch_med = 1 + r['col_ch'] / n
        if r['desbordada']:
            oa_med, oa_teo = 'no aplica', 'infinito'
        else:
            oa_med = f'{1 + r["col_oa"] / n:.2f}'
            teo = esperado_lineal(alpha)
            oa_teo = 'infinito' if teo == float('inf') else f'{teo:.2f}'
        print(f'{alpha:>7.2f} {ch_med:>13.2f} {esperado_chaining(alpha):>14.2f} '
              f'{oa_med:>14} {oa_teo:>15}')

    # --- Donde empieza a degradarse el sondeo lineal ---
    print('\n--- Degradacion del sondeo lineal cerca del umbral ---')
    print(f'{"alpha":>7} {"sondeos/insercion":>19} {"cluster maximo":>16}')
    for a in [0.50, 0.70, 0.75, 0.80, 0.85, 0.90, 0.95, 0.99]:
        n = int(a * M)
        r = medir_colisiones_reales(n, M, 5)
        print(f'{a:>7.2f} {1 + r["col_oa"] / n:>19.2f} {r["cluster_max"]:>16.1f}')

def actividad6():
    _titulo('ACTIVIDAD 6 - Indice invertido')
    indice = construir_indice_invertido(DOCUMENTOS)
    total_entradas = sum(len(v) for v in indice.values())
    print(f'Documentos indexados : {len(DOCUMENTOS)}')
    print(f'Vocabulario          : {len(indice)} terminos unicos')
    print(f'Entradas del indice  : {total_entradas}')
    print(f'Documentos por termino (promedio): {total_entradas / len(indice):.2f}')

    print('\n--- Terminos mas frecuentes ---')
    for palabra, docs in sorted(indice.items(), key=lambda x: -len(x[1]))[:5]:
        print(f'  {palabra:16} -> {sorted(docs)}')

    print('\n--- Consultas AND (deben aparecer todos los terminos) ---')
    for q in ['algoritmos', 'estructuras datos', 'tablas hash',
              'arboles grafos', 'datos hash arboles']:
        ids = buscar_and(indice, q)
        print(f'  {q!r:24} -> {len(ids)} resultado(s): {ids}')
        for i in ids:
            print(f'      [{i}] {DOCUMENTOS[i]}')

    print('\n--- La misma consulta con AND y con OR ---')
    for q in ['arboles grafos', 'tablas hash']:
        a, o = buscar_and(indice, q), buscar_or(indice, q)
        print(f'  {q!r:18} AND -> {a}')
        print(f'  {"":18} OR  -> {o}')

    print('\n--- Ordenacion por relevancia (numero de terminos coincidentes) ---')
    q = 'algoritmos datos busqueda'
    for doc_id, puntaje in documentos_por_relevancia(indice, q):
        print(f'  {puntaje} termino(s)  [{doc_id}] {DOCUMENTOS[doc_id]}')

    # --- Comprobaciones ---
    assert buscar_and(indice, 'tablas hash') == [4, 8]
    assert buscar_and(indice, 'palabrainexistente') == []
    assert set(buscar_or(indice, 'arboles grafos')) == {5, 6, 8}
    assert buscar_and(indice, '') == []
    print('\nComprobaciones del indice invertido: OK')

    # --- Por que el indice invertido gana al barrido secuencial ---
    print('\n--- Indice invertido frente a barrido secuencial ---')
    rng = random.Random(7)
    palabras_base = [f'termino{i}' for i in range(2000)]
    corpus = {i: ' '.join(rng.choices(palabras_base, k=12)) for i in range(20000)}

    t0 = time.perf_counter()
    indice_grande = construir_indice_invertido(corpus)
    t_construir = (time.perf_counter() - t0) * 1000

    def barrido_secuencial(docs, palabra):
        return sorted(i for i, t in docs.items() if palabra in t.split())

    consultas = rng.sample(palabras_base, 50)

    t0 = time.perf_counter()
    for q in consultas:
        indice_grande.get(q, set())
    t_idx = (time.perf_counter() - t0) * 1000

    t0 = time.perf_counter()
    for q in consultas:
        barrido_secuencial(corpus, q)
    t_sec = (time.perf_counter() - t0) * 1000

    print(f'  Corpus: {len(corpus):,} documentos, {len(indice_grande):,} terminos')
    print(f'  Construir el indice (una sola vez) : {t_construir:8.2f} ms')
    print(f'  50 consultas con el indice         : {t_idx:8.3f} ms')
    print(f'  50 consultas por barrido           : {t_sec:8.2f} ms')
    print(f'  El indice es {t_sec / t_idx:,.0f} veces mas rapido en las consultas')
    print(f'  Se amortiza tras {t_construir / (t_sec / len(consultas)):.1f} consultas')

def investigacion():
    _titulo('INVESTIGACION - Hashing perfecto minimo')
    rng = random.Random(2026)

    # --- 1. Verificacion: la funcion es biyectiva sobre [0, n) ---
    print('--- 1. Verificacion de la propiedad de hash perfecto minimo ---')
    for n in [10, 100, 1000, 10000]:
        claves = claves_mph(n, rng)
        f = HashPerfectoMinimo(claves)
        indices = [f(k) for k in claves]
        assert sorted(indices) == list(range(n)), 'no es una biyeccion'
        print(f'  n = {n:>6}: {f}')
        print(f'            indices = {{0, ..., {n - 1}}} sin repetir  OK')

    # --- 2. Efecto del parametro c sobre los intentos de peeling ---
    print('\n--- 2. Efecto de c (vertices por clave) sobre el peeling ---')
    print(f'  {"c":>5} {"m/n":>6} {"intentos":>9} {"bits/clave":>11} {"resultado":>12}')
    n = 5000
    claves = claves_mph(n, rng)
    for c in [1.10, 1.15, 1.20, 1.23, 1.30, 1.50]:
        try:
            t0 = time.perf_counter()
            f = HashPerfectoMinimo(claves, c=c, max_intentos=8, semilla=5)
            ms = (time.perf_counter() - t0) * 1000
            print(f'  {c:>5.2f} {f._m / n:>6.2f} {f._intentos:>9} '
                  f'{f.bits_por_clave:>11.2f} {"OK " + f"{ms:.0f} ms":>12}')
        except RuntimeError:
            print(f'  {c:>5.2f} {"":>6} {">8":>9} {"":>11} {"fallo":>12}')
    print('  El umbral teorico del peeling de hipergrafos 3-partitos es c = 1.22.')

    # --- 3. Construccion frente a consulta: cuando se amortiza ---
    print('\n--- 3. Costo de construccion frente a la consulta ---')
    print(f'  {"n":>7} {"construir MPH":>15} {"construir dict":>15} '
          f'{"MPH us/cons":>13} {"dict us/cons":>13}')
    filas = []
    for n in [1000, 5000, 20000, 50000]:
        claves = claves_mph(n, rng)
        muestras = [rng.choice(claves) for _ in range(2000)]

        t0 = time.perf_counter()
        f = HashPerfectoMinimo(claves)
        t_mph = (time.perf_counter() - t0) * 1000

        t0 = time.perf_counter()
        d = {k: i for i, k in enumerate(claves)}
        t_dict = (time.perf_counter() - t0) * 1000

        for k in muestras[:200]:
            f(k); _ = d[k]
        t0 = time.perf_counter()
        for k in muestras:
            f(k)
        us_mph = (time.perf_counter() - t0) * 1e6 / len(muestras)
        t0 = time.perf_counter()
        for k in muestras:
            _ = d[k]
        us_dict = (time.perf_counter() - t0) * 1e6 / len(muestras)

        filas.append((n, t_mph, t_dict, us_mph, us_dict, f.bits_por_clave))
        print(f'  {n:>7} {t_mph:>12.1f} ms {t_dict:>12.2f} ms '
              f'{us_mph:>13.2f} {us_dict:>13.2f}')

    print('\n  En Python puro el MPH es MAS LENTO por consulta que el dict nativo,')
    print('  porque dict esta implementado en C. La ventaja del MPH no es la')
    print('  velocidad sino el ESPACIO: no almacena las claves.')

    # --- 4. Comparacion de memoria ---
    print('\n--- 4. Memoria: el MPH no guarda las claves ---')
    print(f'  {"n":>7} {"dict (bytes)":>14} {"MPH g[] (bytes)":>17} '
          f'{"bits/clave":>11} {"factor":>8}')
    import sys
    for n in [1000, 10000, 50000]:
        claves = claves_mph(n, rng)
        d = {k: i for i, k in enumerate(claves)}
        bytes_dict = sys.getsizeof(d) + sum(sys.getsizeof(k) for k in claves)
        f = HashPerfectoMinimo(claves)
        bytes_mph = math.ceil(2 * f._m / 8)        # g con 2 bits por vertice
        print(f'  {n:>7} {bytes_dict:>14,} {bytes_mph:>17,} '
              f'{f.bits_por_clave:>11.2f} {bytes_dict / bytes_mph:>7.0f}x')
    print('  El dict guarda las claves completas; el MPH solo el arreglo g.')
    print('  Contrapartida: el MPH NO puede saber si una clave pertenece al')
    print('  conjunto; devuelve un indice valido para cualquier entrada.')

    # --- 5. El falso positivo del MPH ---
    print('\n--- 5. Limitacion: el MPH no verifica la pertenencia ---')
    claves = claves_mph(1000, rng)
    f = HashPerfectoMinimo(claves)
    d = {k: i for i, k in enumerate(claves)}
    intrusa = 'clavequenoestaenelconjunto'
    assert intrusa not in d
    print(f'  clave ausente {intrusa!r}:')
    print(f'    dict -> KeyError (detecta la ausencia)')
    print(f'    MPH  -> devuelve {f(intrusa)}, un indice valido pero sin sentido')
    print('  Para detectarlo hay que almacenar tambien las claves o un resumen')
    print('  (fingerprint) de cada una, lo que anade entre 8 y 16 bits por clave.')


def preguntas():
    pregunta1()
    pregunta2()
    pregunta3()
    pregunta4()


if __name__ == '__main__':
    opciones = {
        '1': actividad1, '2': actividad2, '3': actividad3,
        '4': actividad4, '6': actividad6,
        'mph': investigacion, 'preguntas': preguntas,
    }
    arg = sys.argv[1] if len(sys.argv) > 1 else 'todo'
    if arg in opciones:
        opciones[arg]()
    elif arg == 'todo':
        for fn in [actividad1, actividad2, actividad3, actividad4,
                   actividad6, investigacion]:
            fn()
        print('\nTODAS LAS ACTIVIDADES PASARON')
        print('Para las preguntas de analisis: '
              'python3 Practica_S07_TablaHash_ApellidoNombre.py preguntas')
    else:
        print(f'Opcion no reconocida: {arg!r}')
        print(f'Use una de: {", ".join(opciones)}  o  todo')
