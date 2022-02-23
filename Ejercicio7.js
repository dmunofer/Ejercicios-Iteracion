Algoritmo conversión2E
	# La representación de `n' en base `BASE'.

Entrada
	n : ENTERO		# El número entero a convertir
	BASE : ENTERO		# La base de conversión

Resultado : CADENA

variable
	dividendo : ENTERO ← abs(n)
	q, r : ENTERO	
		# Generan las series de los cocientes y de los restos
		# de `dividendo' por `BASE'
	k : ENTERO		# El número de cocientes ya calculados

inicialización
	Resultado ← CADENA_VACIA	# El resultado actual
	k ← 0

realización
	hasta que dividendo < BASE
		invariante
		#(H) : la siguiente división a realizar es 				
  #	la de `dividendo' por `BASE';
#	el resultado parcial es Resultado
		#	k es el número de divisiones realizadas

			dividendo = abs(n) x BASE-k

		variante de control
			cociente(dividendo, BASE)

	repetir
		q ← cociente(dividendo, BASE)
		r ← resto(dividendo, BASE)

		afirmación
		#(H) : la siguiente división a realizar es la				# de `q' por `BASE'; el resultado parcial es				# Resultado a aumentar de `r' en cifra
		# Le número de divisiones realizadas es k+1
			
			dividendo = abs(n) x BASE-k-1

		Resultado ←	SEPARADOR ⊕ cadena(cifra(r))
				⊕ Resultado

		afirmación
		#(H) : la siguiente división a realizar es la 			
  # de `q' por `BASE'; el resultado parcial es 				
  # Resultado
		# El número de divisiones realizadas es k+1

			dividendo = abs(n) x BASE-k-1
			q = abs(n) x BASE-k

		k ← k+1
		dividendo ← q

		afirmación
		#(H) : la siguiente división a realizar es la 			
  # de `dividendo' por `BASE'; el resultado parcial 			
  # es Resultado
		# El número de divisiones efectuadas es k

			dividendo = abs(n) x BASE-k

	fin repetir

	# Aumentar Resultado en la última cifra…
	Resultado ← cadena(cifra(dividendo))⊕ Resultado

	# … y el signo de `n'
	Resultado ← cadena(signo_c(n)) ⊕ Resultado

fin conversión2E
