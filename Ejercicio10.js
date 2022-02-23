tipo PERSONA estructura
	identificador : ENTERO
	        edad : ENTERO
	   identidad : IDENTIDAD

	padre : ENTERO
	madre : ENTERO
fin PERSONA


Algoritmo 1: Cálculo de los identificadores de las personas de 20 a 30 años

algoritmo edades
	# Selección de los identificadores de las personas por franja
	# de edades.

Entrada
	familias : TABLA[PERSONA]	# El objetivo de la selección
	 edad_min : ENTERO	# El límite de base de la selección
	 edad_max : ENTERO	# El límite superior

Resultado : TABLA[ENTERO][1, 500]

precondición
	familias ≠ NULO
	 edad_min ≠ NULO ; edad_max ≠ NULO

constante
	MIN : ENTERO ← índice_min(familias)
	MAX : ENTERO ← índice_max(familias)

	MIN_EDADES : ENTERO ← índice_min(Resultado)
	MAX_EDADES : ENTERO ← índice_max(Resultado)

	  INFINITO : ENTERO ← ENTERO_MIN
		# El número entero más pequeño utilizable
	HUERFANO : ENTERO ← INFINITO
	  BORRADO : ENTERO ← HUERFANO + 1
	    VACIO : ENTERO ← HUERFANO + 2

variable
	i : ENTERO	
		# Índice de la siguiente celda a observar
	j : ENTERO	
		# Índice siguiente celda de Resultado a inicializar

inicialización
	i ← MIN ; j ← MIN_EDADES
	Resultado[MIN_EDADES] ← VACIO

	afirmación
		i > MIN y j > MIN_EDADES =>
		Las celdas de sub_tabla(Resultado, MIN_EDADES, j-1)
		se inicializan con los identificadores de las celdas 
		de sub_tabla(familias, MIN, i-1) donde los
		identificadores no son ni BORRADO ni VACIO y la edad
		está entre `edad_min' y `edad_max'

realización
	hasta que
		familias[i].identificador = VACIO
		o si no i > MAX

		invariante
			???
		variante de control
			MAX -i + 1

	repetir
		si
			familias[i].identificador ≠ BORRADO
		    y entonces
			edad_min ≤ familias[i].edad ≤ edad_max
		entonces
			Resultado[j] ← familias[i].identificador
			j ← j + 1
		fin si

		i ← i + 1
	fin repetir

postcondición
	# Resultado está VACIO cuando los límites de edades no están en
	# orden
	edad_min > edad_max => Resultado[1] = VACIO

	(∀k ∈ ℤ)(
		índice_min(Resultado) ≤ k ≤ índice_max(Resultado)
		=>
		Resultado[k] es el identificador de una persona de edad
		entre `edad_min' y `edad_max' años
		)
fin edades


Algoritmo 2: Envejecer un año a las personas registradas

algoritmo envejecer
	# Envejece la población un año.

Entrada
	familias : TABLA[PERSONA]

precondición
	familias ≠ NULO


constante
	MIN : ENTERO ← índice_min(familias)
	MAX : ENTERO ← índice_max(familias)

	  INFINITO : ENTERO ← ENTERO_MIN
		# El número entero más pequeño utilizable
	HUERFANO : ENTERO ← INFINITO
	  BORRADO : ENTERO ← HUERFANO + 1
	    VACIO : ENTERO ← HUERFANO + 2

variable
	i : ENTERO	# Índice de la siguiente celda a tratar

inicialización
	i ← MIN

realización
	hasta que 
		familias[i].identificador = VACIO 
	    o si no
		i > MAX

		invariante
			???
		variante de control
			MAX – i + 1
	repetir
		si
		    familias[i].identificador ≠ BORRADO
		entonces
		    familias[i].edad ← familias[i].edad + 1
		fin si

		i ← i + 1
	fin repetir

postcondición
	Se han incrementado todos los atributos `edad' de las celdas
	ni VACIO ni BORRADO

fin envejecer


Algoritmo 3: Lista de los identificadores de los huérfanos de padre o de madre.

Algoritmo huérfanos
	# Lista de los identificadores de los huérfanos.

Entrada
	familias : TABLA[PERSONA]

# Tablas de los identificadores de los huérfanos
Resultado : TABLA[ENTERO][1, 500]

precondición
	familias ≠ NULO

constante
	MIN : ENTERO ← índice_min(familias)
	MAX : ENTERO ← índice_max(familias)
	MIN_HUERFANO : ENTERO ← índice_min(Resultado)
	MAX_HUERFANO : ENTERO ← índice_max(Resultado)

	  INFINITO : ENTERO ← ENTERO_MIN
		# El número entero más pequeño utilizable
	HUERFANO : ENTERO ← INFINITO
	  BORRADO : ENTERO ← HUERFANO + 1
	    VACIO : ENTERO ← HUERFANO + 2

variable
	i : ENTERO	
		# Índice de la siguiente celda a tratar
	j : ENTERO
		# Índice de la siguiente celda de Resultado a
		# inicializar

inicialización
	i ← MIN
	j ← MIN_HUERFANO
	Resultado[j] ← VACIO	# Todavía ningún HUERFANO encontrado

realización
	hasta que 
		familias[i].identificador = VACIO 
	    o si no
		i > MAX

		invariante
			???
		variante de control
			MAX – i + 1
	repetir
		si
		    familias[i].identificador ≠ BORRADO
		  y entonces
		    (
		 	  familias[i].padre = HUERFANO
			o
			  familias[i].madre = HUERFANO
		    )
		entonces
		    Resultado[j] ← familias[i].identificador
		    j ← j + 1
		fin si

		i ← i + 1
	fin repetir

postcondición
	Se han registrado en Resultado los identificadores de todos los
	HUERFANOS de las celdas ni VACIO ni BORRADO 

fin huérfanos



Algoritmo padre
	# El identificador del padre de `identidad'.

...
hasta que
	familias[i].identificador = VACIO
    o si no
	i > MAX
repetir
	si
		familia[i].identificador ≠ BORRADO
	    y entonces
		(
		  familia[i].identidad.nombre = identidad.nombre
		y
		  familia[i].identidad.apellido = identidad.apellido
		)
	entonces
		Resultado[j, 1] ← familia[i].identificador
		Resultado[j, 2] ← familia[i].padre
		j ← j + 1
	fin si

	i ← i + 1
fin repetir


Algoritmo unos_hermanos
	# Calcula los hermanos de padre `padre' de los hermanos de
	# `identificador'

Entrada
	familias : TABLA[PERSONA]
	identificador : ENTERO # Persona para la que queremos hermanos
	       padre : ENTERO # Identificador del padre de los hermanos

Resultado : TABLA[ENTERO] # Identificadores miembros de los hermanos

constante
	MAX : ENTERO ← índice_max(familias)

variable
	persona : ENTERO	 # Un identificador de persona
	i : ENTERO	# siguiente hermano/a a registrar

inicialización
	Resultado[1] ← identificador
	i ← 1		# Índice del último hermano identificado
	j ← índice_min(familias)

realización
	persona ← familias[j].identificador
		# siguiente persona a observar en `familias'

	hasta que persona = VACIO o si no j > MAX repetir
		invariante
			???
		variante de control
			MAX – i + 1

		si
			persona ≠ BORRADO
		    y
			familias[j].padre = padre
		entonces
			i ← i + 1
			Resultado[i] ← persona
		fin si
	
		j ← j + 1
	fin repetir

	Resultado[i + 1] ← VACIO	# Marca el final de los hermanos

postcondición
	

fin unos_hermanos
