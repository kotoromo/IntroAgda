
# Una introducción a una introducción de Agda
### García Fierros Nicky

## Introducción

Agda es tanto un lenguaje de programación (funcional) como un asistente de
pruebas (Vease [PROOF = PROGRAM - Samuel Mimram](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/course.pdf). De acuerdo con la [documentación
oficial de Agda](https://agda.readthedocs.io/en/v2.6.3/getting-started/what-is-agda.html), Agda es una extensión de la teoría de tipos de Martin-Löf, por lo que
su poder expresivo es adecuado para escribir pruebas y especificaciones de
objetos matemáticos. De esta forma, Agda también es una herramienta para la
formalización de las matemáticas. En tanto que para poder aprovechar todo el
poder de Agda como asistente de pruebas y herramienta de formalización de
matemáticas se requiere estudiar la teoría de tipos antes mencionada, en esta
breve pero concisa introducción no se tocarán los detalle; sin embargo
considero importante mencionar que, yo como autor, el acercamiento que he
tenido con la teoría de tipos de Martin-Löf y Agda ha sido gracias a la
teoría homotópica de tipos, de modo que mi forma de pensar sobre lo que se
presentará en este trabajo no podría empatar directamente con la teoría sobre
la cual se fundamenta Agda.

Hay mucho que decir sobre la relación entre la lógica, las categorías y los
tipos; sin emargo me limitaré a mencionar la correspondencia
Curry-Howard-Lambek por muy encima, y una breve mención de tipos dependientes y
su interpretación tanto lógica como categórica.

### Correspondencia Curry-Howard-Lambek

En **[The Formulae-As-Types Notion of Construction](https://www.cs.cmu.edu/~crary/819-f09/Howard80.pdf)**, un artículo escrito por el lógico Alvin Howard en
1980 menicona que Curry sugirió una relación entre los combinadores del
cálculo lambda y axiomas de la lógica. En este mismo escrito, Howard formaliza
las observaciones hechas por Curry. Por otro lado, a inicios de los 70's el
matemático Joachim Lambek demuestra que las categorías cartesianas cerradas y
la lógica combinatoria tipada comparten una teoría ecuacional en común.

La correspondencia es entonces

|     Tipos      |     Lógica     |      Categorías     |
| -------------  | -------------- | ------------------- |
|      𝟙         |       ⊤        |  Objeto terminal    |
|      𝟘         |       ⊥        |  Objeto inicial     |
|      →         |       ⊃        |  Flecha             |
|      ×         |       ∧        |  Producto           |
|      +         |       ∨        |  Coproducto         |

Es importante señalar que, a diferencia de la teoría de conjuntos, los tipos
producto y función son conceptos primitivos.

La forma de construir términos de un tipo producto coincide con aquella de la
teoría de categorías. Dados $a : A$ y $b : B$ podemos construir $(a , b) : A × B$.
Hablaremos un poco más sobre cómo "acceder" a los elementos que componen un tipo
producto cuando entremos bien en materia sobre usar a Agda como un asistente de
prueba.

Por otro lado, la forma de construir un tipo flecha es mediante un proceso de
**abstracción**. Si tenemos un término, y observamos que podemos abstraer cierto
comportamiento de interés, entonces podemos introducir un tipo flecha que
abstrae el comportamiento deseado, de forma análoga a como solemos hacerlo en
matemáticas. Si, por ejemplo, observamos que la sucesión 0, 1, 2, 4, 16, 32, ...
presenta un comportamiento cuadrático, podemos abstraer este comportamiento
escribiendo una representación simbólica de este en términos de nuestro lenguaje
matemático:
$$
f(x) = x^2
$$

Para restringir más dicho comportamiento en función de la clase de términos que
queremos considerar en nuestra abstracción, introducimos dominios y codominios.

$$
f : ℕ → ℕ
$$

de modo que sólo permitimos que $f$ "funcione" con naturales, y garantizamos que
tras hacer cualquier cómputo con $f$, el número que nos devuelve es un número
natural.

De forma análoga, el proceso de abstracción involucrado en la introducción
de un tipo flecha involucra un término `t : B`, del cual abstraemos `x : A`
y garantizamos que tras cualquier cómputo realizado con este tipo flecha
obtenemos otro término de tipo `B`. Expresamos esto con la siguiente
sintaxis:

```haskell
λx . t : A → B
```

### Π-types, Σ-types, lógica y categorías.

La teoría de tipos de Martin-Löf permite trabajar con tipos que dependen de
otros; es de esta forma que son **tipos dependientes**. Se introducen los tipos
de funciones dependientes, y los tipos coproducto.

#### Π-types

El HoTT Book menciona que los elementos (términos) de un tipo Π son funciones
cuyo tipo codominio puede variar según el elemento del dominio hacia el cual
se aplica la función. En virtud de este comportamiento familiar para aquellas
personas que han estudiado teoría de conjuntos es que reciben el nombre de Π,
pues el producto cartesiano generalizado tiene este mismo comportamiento.

Dado un conjunto $A$, y una familia $B$ indizada por $A$, el producto cartesiano generalizado es
$$
\prod\limits_{a ∈ A} B(a) = \{ f: A → \bigcup\limits_{a ∈ A}B(a)\ \vert\ ∀a ∈ A . f(a) ∈ B(a) \}
$$

En teoría de tipos escribimos `:` en lugar de `∈`, pero la sintaxis es prácticamente la misma.
Dado un tipo `A`, y una familia `B:A → Type`, podemos construir el tipo de funciones
dependientes

```haskell
Π(a:A) B(a) : Type
```

Intuitivamente, y en efecto así ocurre, si `B` es una familia constante, entonces

```haskell
Π(a:A) B(a) ≡ (A → B)
```

De esta forma, el tipo Π generaliza a los tipos flecha. Estos tipos además permiten el
polimorfismo de funciones. Una función polimorfa es aquella que toma un tipo como
argumento y actúa sobre los elementos de dicho tipo. Esto debería recordarle a usted
del ∀ en la lógica. Una observación pertinente es que los tipos producto se pueden
pensar como una versión "no dependiente" en cierto sentido de los tipos Π.

#### Σ-types

Así como los tipos Π generalizan a los tipos flecha, los tipos Σ generalizan a los
tipos producto, en tanto que permiten que el elemento en la "segunda coordenada"
dependa del elemento en la "primera coordenada". Obsevese que este comportamiento
es el mismo que permite el coproducto de la categoría de conjuntos (la unión disjunta).

```haskell
Σ(x:A) B(x)
```

Intuitivamente, y de nuevo es cierto que, si $B$ es constante, entonces
$$
\right( \sum\limits_{x : A} B \left) ≡ (A × B)
$$

Así como el tipo Π se puede identificar con el ∀ en lógica, el tipo Σ se puede
identificar con el cuantificador ∃. Una observación adicional pertinente
respecto a los tipos Σ es que los tipos + son una versión "no dependiente" en
cierto sentido de los tipos Σ.

### En resumen

Resumiendo algunos comentarios relevantes a esta pequeña introducción a la
teoría de tipos de Martin-Löf, tenemos la siguiente tabla.

| Tipos | Lógica | Categorías |
| ----- | ------ | ---------- |
| Σ     | ∃      | coproducto |
| Π     | ∀      | producto   |

## Probando tautologías de la lógica proposicional con Agda

El poder expresivo de la teoría de tipos de Martin-Löf (y por extensión la teoría
homotópica de tipos) permite identificar proposiciones matemáticas con tipos, y sus
demostraciones con términos de un tipo dado. De esta forma, si ocurre que el tipo
tiene por lo menos un término, entonces podemos permitir decir que tenemos una
demostración de dicha proposición.
En HoTT las proposiciones (de la lógica proposicional) corresponden a una clase
particular de tipos, en tanto que [en la lógica de primer orden no hay forma de distinguir entre una prueba de otra](https://homotopytypetheory.org/book/).
Estas tecnicalidades se mencionan con el propósito de incitar a la persona leyendo
o escuchando esto a investigar más por su cuenta, pues
para propósitos de esta exposición haremos uso del tipo `Set` de Agda, que renombraremos
a `Type` para hacer énfasis en este paradigma de "Proposiciones como tipos".

Iniciamos escribiendo al inicio de todo nuestro archivo con extensión `.agda` o `.lagda.md`
las siguientes cláusulas:

<pre class="Agda">
<a id="8018" class="Keyword">open</a> <a id="8023" class="Keyword">import</a> <a id="8030" href="Data.Product.html" class="Module">Data.Product</a> <a id="8043" class="Keyword">renaming</a> <a id="8052" class="Symbol">(</a><a id="8053" href="Data.Product.html#1167" class="Function Operator">_×_</a> <a id="8057" class="Symbol">to</a> <a id="8060" class="Function Operator">_∧_</a><a id="8063" class="Symbol">)</a>

<a id="Type"></a><a id="8066" href="Presentacion.html#8066" class="Function">Type</a> <a id="8071" class="Symbol">=</a> <a id="8073" href="Agda.Primitive.html#320" class="Primitive">Set</a>

</pre>
En la primera línea le pedimos a Agda por favor y con mucho cariño que de la
biblioteca estándar importe el tipo Product y que además renombre el operador `×`
a `∧`. En la segunda línea renombramos al tipo `Set` como `Type`.

Para pedirle a Agda, de nuevo por favor y con mucho cariño, que nos diga si
lo que hemos escrito hasta el momento está bien escrito y bien tipado
presionamos la combinación `C-c C-l` en emacs o en vscode con la extensión `agda-mode`.
Si todo está bien, deberíamos ver colorcitos en el código Agda que escribimos y
ningún mensaje al fondo de emacs o de vscode.

Ya con nuestro preámbulo listo, empecemos a demostrar pero no sin antes dar el crédito
correspondiente. La gran mayoría de cosas que se expondrán a continuación fueron tomadas
de las siguientes fuentes:

  * [Propositional Logic in Agda - Samuel Mimram](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/TD/5.propositional.html)
  * [The HoTT Game](https://homotopytypetheory.org/2021/12/01/the-hott-game/)
  * [Agda in a hurry - Martin Escardó](https://www.cs.bham.ac.uk/~mhe/fp-learning-2017-2018/html/Agda-in-a-Hurry.html)
  * [HoTTEST School Agda Notes - Martin Escardó](https://martinescardo.github.io/HoTTEST-Summer-School/)
  * [HoTT UF in Agda - Martin Escardó](https://www.cs.bham.ac.uk/~mhe/HoTT-UF-in-Agda-Lecture-Notes/HoTT-UF-Agda.html#contents)
  *[Proof = Program - Samuel Mimram](https://www.lix.polytechnique.fr/Labo/Samuel.Mimram/teaching/INF551/course.pdf)

#### Proposición
Sean $A, B$ proposiciones. Entonces $A ∧ B ⇔ B ∧ A$.

##### Demostración

Recordando que bajo nuestro paradigma en uso las proposiciones son tipos,
codificamos nuestra proposición como un tipo y, para demostrar la proposición
buscamos definir un término bien tipado del tipo de nuestra proposición.

```haskell
∧-comm : {A B : Type} → A ∧ B → B ∧ A
∧-comm = ？ 

```

Como no sabemos ni pío de Agda, le preguntamos a Agda qué opina que debería
ser la definición de nuestro término que, a final de cuentas será nuestra
prueba. Esto lo hacemos escribiendo el signo de interrogación despues de el signo
de igualdad. Si le pedimos a Agda que verifique si nuestro programa está bien tipado,
apareceran mensajes en la parte de abajo de emacs/vscode y los símbolos `{ }0` en
donde habíamos puesto nuestro preciado símbolo de interrogación. Estos símbolos
significan que ahí hay un **hueco de meta**.
Los mensajes leen

```haskell
?0 : A ∧ B → B ∧ A
```

Lo que denotan los símbolos `?0` es que nuestra meta `0` es la de producir un término
del tipo `A ∧ B → B ∧ A`. Podemos pedirle a Agda que nos de más información sobre nuestro
problema (Contexto y Meta) al posicionar el cursor en el hueco de meta
mediante la combinación de teclas `C-c C-,` en emacs.

Veremos que ahora nos muestra mensajes muy distintos a los anteriores.
Nos dice que en nuestra declaración del término que necesitamos debemos asumir que
`B` y `A` son tipos. Quizás para esta situación no es muy reveladora la información
que brinda Agda, pero en otras situaciones brinda información bastante útil.

Podemos pedirle a Agda que nos de más pistas, con base en la naturaleza de los
términos de los tipos que queremos producir. Para esto, de nuevo con el cursor en el hueco
de meta, presionamos la combinación de teclas `C-c C-r` en emacs/vscode para "refinar la meta".

```haskell

∧-comm : {A B : Type} → A ∧ B → B ∧ A
∧-comm = λ x → { }1

```

Al hacer esto, notamos que agda modifica el hueco y las metas se modifican acordemente.
Ahora nuestra meta es producir un término de tipo `B ∧ A`. Si volvemos a pedirle a Agda
el contexto y meta del problema, veremos que ahora tenemos a nuestra disposición
un término `x : A ∧ B`, con el cual podemos producir un término de tipo `B ∧ A`.
Si de nuevo le pedimos a Agda que refine la meta, tendremos ahora dos metas nuevas:
producir un término de tipo `B` y otro término de tipo `A`.

```haskell

∧-comm : {A B : Type} → A ∧ B → B ∧ A
∧-comm = λ x → { }1 , { }2

```

```haskell

∧-comm : {A B : Type} → A ∧ B → B ∧ A
∧-comm = λ x → {aa}0, {aa}1 

```

De aquí, podemos proceder de al menos tres formas distintas.
  * Podemos recordar que en la teoría de tipos de Martin-Löf (MLTT) el tipo producto
  es una noción primitiva, y por lo tanto Agda debe de implementar de forma "nativa"
  un eliminador izquierdo y derecho para el tipo producto.

  * Podemos probar un lema (redundante bajo la observación anterior)
  * Podemos aprovechar las bondades de Agda y su pattern matching para poder construir el término
  que queremos en virtud de la sintaxis que tienen los términos del tipo producto.

En tanto que para lo primero habría que irse a la documentación de Agda, y podríamos
usar lo tercero para probar el lema de la segunda opción, mejor probamos juntos el lema
y las otras opciones se quedan como ejercicio.

En MLTT, los términos del tipo producto se forman según el siguiente juicio:

```haskell

Γ ⊢ a : A      Γ ⊢ b : B
--------------------------[×-intro]
Γ ⊢ (a , b) : A × B

```

De esta forma, aprovechando el pattern matching de Agda podemos escribir la siguiente demostración
para el lema

#### Lema

Sean $A$, $B$ proposiciones. Entonces $A ∧ B ⊃ A$ y $A ∧ B ⊃ B$.


##### Demostración

<pre class="Agda"><a id="∧-el"></a><a id="13299" href="Presentacion.html#13299" class="Function">∧-el</a> <a id="13304" class="Symbol">:</a> <a id="13306" class="Symbol">{</a><a id="13307" href="Presentacion.html#13307" class="Bound">A</a> <a id="13309" href="Presentacion.html#13309" class="Bound">B</a> <a id="13311" class="Symbol">:</a> <a id="13313" href="Presentacion.html#8066" class="Function">Type</a><a id="13317" class="Symbol">}</a> <a id="13319" class="Symbol">→</a> <a id="13321" href="Presentacion.html#13307" class="Bound">A</a> <a id="13323" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="13325" href="Presentacion.html#13309" class="Bound">B</a> <a id="13327" class="Symbol">→</a> <a id="13329" href="Presentacion.html#13307" class="Bound">A</a>
<a id="13331" href="Presentacion.html#13299" class="Function">∧-el</a> <a id="13336" class="Symbol">(</a><a id="13337" href="Presentacion.html#13337" class="Bound">a</a> <a id="13339" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="13341" href="Presentacion.html#13341" class="Bound">b</a><a id="13342" class="Symbol">)</a> <a id="13344" class="Symbol">=</a> <a id="13346" href="Presentacion.html#13337" class="Bound">a</a>

<a id="∧-er"></a><a id="13349" href="Presentacion.html#13349" class="Function">∧-er</a> <a id="13354" class="Symbol">:</a> <a id="13356" class="Symbol">{</a><a id="13357" href="Presentacion.html#13357" class="Bound">A</a> <a id="13359" href="Presentacion.html#13359" class="Bound">B</a> <a id="13361" class="Symbol">:</a> <a id="13363" href="Presentacion.html#8066" class="Function">Type</a><a id="13367" class="Symbol">}</a> <a id="13369" class="Symbol">→</a> <a id="13371" href="Presentacion.html#13357" class="Bound">A</a> <a id="13373" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="13375" href="Presentacion.html#13359" class="Bound">B</a> <a id="13377" class="Symbol">→</a> <a id="13379" href="Presentacion.html#13359" class="Bound">B</a>
<a id="13381" href="Presentacion.html#13349" class="Function">∧-er</a> <a id="13386" class="Symbol">(</a><a id="13387" href="Presentacion.html#13387" class="Bound">a</a> <a id="13389" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="13391" href="Presentacion.html#13391" class="Bound">b</a><a id="13392" class="Symbol">)</a> <a id="13394" class="Symbol">=</a> <a id="13396" href="Presentacion.html#13391" class="Bound">b</a>

</pre>Una observación pertinete es que al refinar y obtener los dos huecos anteriormente,
Agda nos está diciendo que utilicemos la regla de introducción del tipo producto, tal y como
lo hicimos al probar nuestro lema, para generar el término que deseamos. Entonces el proceso de
refinamiento de meta corresponde a aplicar una regla de introducción.

Ya armados con nuestro lema, podemos demostrar lo que queríamos en un inicio.
Para "darle" a Agda los términos tenemos dos opciones, que realmente son la misma:
  * Escribir sobre el hueco el término y luego presionar `C-c C-SPC` ó,
  * Presionar sobre el hueco `C-c C-SPC`.

Antes de rellenar ambos huecos, prueba usando la combinación `C-c C-n`
en alguno de los huecos, y escribiendo `∧-er x` o `∧-el x`. Encontrarás que Agda
**normaliza** el término que escribiste. Al escribir `∧-er x` regresa `proj₂ x` el cual
es el resultado de aplicar el eliminador "nativo" del tipo producto sobre el término `x`.
Tras darle a Agda los términos necesarios, terminamos nuestra prueba. 

<pre class="Agda">
<a id="∧-comm"></a><a id="14434" href="Presentacion.html#14434" class="Function">∧-comm</a> <a id="14441" class="Symbol">:</a> <a id="14443" class="Symbol">{</a><a id="14444" href="Presentacion.html#14444" class="Bound">A</a> <a id="14446" href="Presentacion.html#14446" class="Bound">B</a> <a id="14448" class="Symbol">:</a> <a id="14450" href="Presentacion.html#8066" class="Function">Type</a><a id="14454" class="Symbol">}</a> <a id="14456" class="Symbol">→</a> <a id="14458" href="Presentacion.html#14444" class="Bound">A</a> <a id="14460" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="14462" href="Presentacion.html#14446" class="Bound">B</a> <a id="14464" class="Symbol">→</a> <a id="14466" href="Presentacion.html#14446" class="Bound">B</a> <a id="14468" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="14470" href="Presentacion.html#14444" class="Bound">A</a>
<a id="14472" href="Presentacion.html#14434" class="Function">∧-comm</a> <a id="14479" class="Symbol">=</a> <a id="14481" class="Symbol">λ</a> <a id="14483" href="Presentacion.html#14483" class="Bound">x</a> <a id="14485" class="Symbol">→</a> <a id="14487" class="Symbol">(</a><a id="14488" href="Presentacion.html#13349" class="Function">∧-er</a> <a id="14493" href="Presentacion.html#14483" class="Bound">x</a><a id="14494" class="Symbol">)</a> <a id="14496" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="14498" class="Symbol">(</a><a id="14499" href="Presentacion.html#13299" class="Function">∧-el</a> <a id="14504" href="Presentacion.html#14483" class="Bound">x</a><a id="14505" class="Symbol">)</a> 

</pre>
En conclusión, el termino `∧-comm = λ x → (∧-er x) , (∧-el x)` es prueba/testigo de que
el tipo `∧-comm : {A B : Type} → A ∧ B → B ∧ A` no es vacío y por lo tanto es una proposición
"verdadera".

Notemos que esta demostración tiene su contraparte categórica.
# TODO: Insertar dibujin

Y también tiene su contraparte en el cálculo de secuentes.
![secuentes conmut](./img/secuentes_comm.png)

#### Proposición

Sean $A, B$ proposiciones. Entonces $A ⊃ B ⊃ A$

##### Demostración

<pre class="Agda">
<a id="prop1"></a><a id="15001" href="Presentacion.html#15001" class="Function">prop1</a> <a id="15007" class="Symbol">:</a> <a id="15009" class="Symbol">{</a><a id="15010" href="Presentacion.html#15010" class="Bound">A</a> <a id="15012" href="Presentacion.html#15012" class="Bound">B</a> <a id="15014" class="Symbol">:</a> <a id="15016" href="Presentacion.html#8066" class="Function">Type</a><a id="15020" class="Symbol">}</a> <a id="15022" class="Symbol">→</a> <a id="15024" href="Presentacion.html#15010" class="Bound">A</a> <a id="15026" class="Symbol">→</a> <a id="15028" href="Presentacion.html#15012" class="Bound">B</a> <a id="15030" class="Symbol">→</a> <a id="15032" href="Presentacion.html#15010" class="Bound">A</a>
<a id="15034" href="Presentacion.html#15001" class="Function">prop1</a> <a id="15040" class="Symbol">=</a> <a id="15042" class="Symbol">λ</a> <a id="15044" href="Presentacion.html#15044" class="Bound">a</a> <a id="15046" class="Symbol">→</a> <a id="15048" class="Symbol">(λ</a> <a id="15051" href="Presentacion.html#15051" class="Bound">b</a> <a id="15053" class="Symbol">→</a> <a id="15055" href="Presentacion.html#15044" class="Bound">a</a><a id="15056" class="Symbol">)</a>

</pre>
#### Proposición

Sean $A, B, C$ proposiciones. Si $A ⊃ B$ y $B ⊃ C$ entonces $A ⊃ C$.

##### Demostración

<pre class="Agda"><a id="15180" class="Comment">-- Si uno tiene muchas ganas,</a>
<a id="15210" class="Comment">-- puede escribir la proposición en notación de cálculo de secuentes</a>

<a id="→-trans"></a><a id="15280" href="Presentacion.html#15280" class="Function">→-trans</a> <a id="15288" class="Symbol">:</a> <a id="15290" class="Symbol">{</a><a id="15291" href="Presentacion.html#15291" class="Bound">A</a> <a id="15293" href="Presentacion.html#15293" class="Bound">B</a> <a id="15295" href="Presentacion.html#15295" class="Bound">C</a> <a id="15297" class="Symbol">:</a> <a id="15299" href="Presentacion.html#8066" class="Function">Type</a><a id="15303" class="Symbol">}</a>
          <a id="15315" class="Symbol">→</a> <a id="15317" class="Symbol">(</a><a id="15318" href="Presentacion.html#15291" class="Bound">A</a> <a id="15320" class="Symbol">→</a> <a id="15322" href="Presentacion.html#15293" class="Bound">B</a><a id="15323" class="Symbol">)</a>
          <a id="15335" class="Symbol">→</a> <a id="15337" class="Symbol">(</a><a id="15338" href="Presentacion.html#15293" class="Bound">B</a> <a id="15340" class="Symbol">→</a> <a id="15342" href="Presentacion.html#15295" class="Bound">C</a><a id="15343" class="Symbol">)</a>
          <a id="15355" class="Comment">------------</a>
          <a id="15378" class="Symbol">→</a> <a id="15380" class="Symbol">(</a><a id="15381" href="Presentacion.html#15291" class="Bound">A</a> <a id="15383" class="Symbol">→</a> <a id="15385" href="Presentacion.html#15295" class="Bound">C</a><a id="15386" class="Symbol">)</a>

<a id="15389" href="Presentacion.html#15280" class="Function">→-trans</a> <a id="15397" href="Presentacion.html#15397" class="Bound">f</a> <a id="15399" href="Presentacion.html#15399" class="Bound">g</a> <a id="15401" class="Symbol">=</a> <a id="15403" class="Symbol">λ</a> <a id="15405" href="Presentacion.html#15405" class="Bound">a</a> <a id="15407" class="Symbol">→</a> <a id="15409" href="Presentacion.html#15399" class="Bound">g</a> <a id="15411" class="Symbol">(</a><a id="15412" href="Presentacion.html#15397" class="Bound">f</a> <a id="15414" href="Presentacion.html#15405" class="Bound">a</a><a id="15415" class="Symbol">)</a>
</pre>#### Proposición

Sea $A$ una proposición. Entonces $A ⊃ A$.

##### Demostración

<pre class="Agda"><a id="id"></a><a id="15511" href="Presentacion.html#15511" class="Function">id</a> <a id="15514" class="Symbol">:</a> <a id="15516" class="Symbol">{</a><a id="15517" href="Presentacion.html#15517" class="Bound">A</a> <a id="15519" class="Symbol">:</a> <a id="15521" href="Presentacion.html#8066" class="Function">Type</a><a id="15525" class="Symbol">}</a> <a id="15527" class="Symbol">→</a> <a id="15529" href="Presentacion.html#15517" class="Bound">A</a> <a id="15531" class="Symbol">→</a> <a id="15533" href="Presentacion.html#15517" class="Bound">A</a>

<a id="15536" href="Presentacion.html#15511" class="Function">id</a> <a id="15539" class="Symbol">=</a> <a id="15541" class="Symbol">λ</a> <a id="15543" href="Presentacion.html#15543" class="Bound">a</a> <a id="15545" class="Symbol">→</a> <a id="15547" href="Presentacion.html#15543" class="Bound">a</a>

</pre>
#### Proposición

Sean $A, B$ proposiciones. Si $A ⊃ B$ y $A$, entonces $B$.

##### Demostración

<pre class="Agda"><a id="→app"></a><a id="15661" href="Presentacion.html#15661" class="Function">→app</a> <a id="15666" class="Symbol">:</a> <a id="15668" class="Symbol">{</a><a id="15669" href="Presentacion.html#15669" class="Bound">A</a> <a id="15671" href="Presentacion.html#15671" class="Bound">B</a> <a id="15673" class="Symbol">:</a> <a id="15675" href="Presentacion.html#8066" class="Function">Type</a><a id="15679" class="Symbol">}</a>
     <a id="15686" class="Symbol">→</a> <a id="15688" class="Symbol">(</a><a id="15689" href="Presentacion.html#15669" class="Bound">A</a> <a id="15691" class="Symbol">→</a> <a id="15693" href="Presentacion.html#15671" class="Bound">B</a><a id="15694" class="Symbol">)</a>
     <a id="15701" class="Symbol">→</a> <a id="15703" href="Presentacion.html#15669" class="Bound">A</a>
     <a id="15710" class="Comment">----------------[App/Modus Ponens]</a>
     <a id="15750" class="Symbol">→</a> <a id="15752" href="Presentacion.html#15671" class="Bound">B</a>

<a id="15755" href="Presentacion.html#15661" class="Function">→app</a> <a id="15760" href="Presentacion.html#15760" class="Bound">f</a> <a id="15762" href="Presentacion.html#15762" class="Bound">a</a> <a id="15764" class="Symbol">=</a> <a id="15766" href="Presentacion.html#15760" class="Bound">f</a><a id="15767" class="Symbol">(</a><a id="15768" href="Presentacion.html#15762" class="Bound">a</a><a id="15769" class="Symbol">)</a>
</pre>
#### Proposición
Sea $A$ una proposición. Entonces $A ⊃ A ∧ A$.

##### Demostración

<pre class="Agda">
<a id="Δ"></a><a id="15870" href="Presentacion.html#15870" class="Function">Δ</a> <a id="15872" class="Symbol">:</a> <a id="15874" class="Symbol">{</a><a id="15875" href="Presentacion.html#15875" class="Bound">A</a> <a id="15877" class="Symbol">:</a> <a id="15879" href="Presentacion.html#8066" class="Function">Type</a><a id="15883" class="Symbol">}</a>
  <a id="15887" class="Symbol">→</a> <a id="15889" href="Presentacion.html#15875" class="Bound">A</a>
  <a id="15893" class="Comment">-------------</a>
  <a id="15909" class="Symbol">→</a> <a id="15911" class="Symbol">(</a><a id="15912" href="Presentacion.html#15875" class="Bound">A</a> <a id="15914" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="15916" href="Presentacion.html#15875" class="Bound">A</a><a id="15917" class="Symbol">)</a>


<a id="15921" href="Presentacion.html#15870" class="Function">Δ</a> <a id="15923" href="Presentacion.html#15923" class="Bound">a</a> <a id="15925" class="Symbol">=</a> <a id="15927" href="Presentacion.html#15511" class="Function">id</a> <a id="15930" href="Presentacion.html#15923" class="Bound">a</a> <a id="15932" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="15934" href="Presentacion.html#15511" class="Function">id</a> <a id="15937" href="Presentacion.html#15923" class="Bound">a</a>
</pre>
#### Proposición
Sean $A, B, C$ proposiciones. Entonces $A × B ⊃ C$ si y solo si $A ⊃ B ⊃ C$
(Hom(A × B, C) ≅ Hom(A, Cᴮ))
##### Demostración

<pre class="Agda">
<a id="currying"></a><a id="16095" href="Presentacion.html#16095" class="Function">currying</a> <a id="16104" class="Symbol">:</a> <a id="16106" class="Symbol">{</a><a id="16107" href="Presentacion.html#16107" class="Bound">A</a> <a id="16109" href="Presentacion.html#16109" class="Bound">B</a> <a id="16111" href="Presentacion.html#16111" class="Bound">C</a> <a id="16113" class="Symbol">:</a> <a id="16115" href="Presentacion.html#8066" class="Function">Type</a><a id="16119" class="Symbol">}</a>
          <a id="16131" class="Symbol">→</a> <a id="16133" class="Symbol">(</a><a id="16134" href="Presentacion.html#16107" class="Bound">A</a> <a id="16136" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="16138" href="Presentacion.html#16109" class="Bound">B</a> <a id="16140" class="Symbol">→</a> <a id="16142" href="Presentacion.html#16111" class="Bound">C</a><a id="16143" class="Symbol">)</a>
          <a id="16155" class="Comment">----------------</a>
          <a id="16182" class="Symbol">→</a> <a id="16184" href="Presentacion.html#16107" class="Bound">A</a> <a id="16186" class="Symbol">→</a> <a id="16188" href="Presentacion.html#16109" class="Bound">B</a> <a id="16190" class="Symbol">→</a> <a id="16192" href="Presentacion.html#16111" class="Bound">C</a>
<a id="16194" href="Presentacion.html#16095" class="Function">currying</a> <a id="16203" class="Symbol">=</a> <a id="16205" class="Symbol">λ</a> <a id="16207" href="Presentacion.html#16207" class="Bound">f</a> <a id="16209" class="Symbol">→</a> <a id="16211" class="Symbol">λ</a> <a id="16213" href="Presentacion.html#16213" class="Bound">a</a> <a id="16215" class="Symbol">→</a> <a id="16217" class="Symbol">λ</a> <a id="16219" href="Presentacion.html#16219" class="Bound">b</a> <a id="16221" class="Symbol">→</a> <a id="16223" href="Presentacion.html#16207" class="Bound">f</a> <a id="16225" class="Symbol">(</a><a id="16226" href="Presentacion.html#16213" class="Bound">a</a> <a id="16228" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="16230" href="Presentacion.html#16219" class="Bound">b</a><a id="16231" class="Symbol">)</a>

<a id="currying2"></a><a id="16234" href="Presentacion.html#16234" class="Function">currying2</a> <a id="16244" class="Symbol">:</a> <a id="16246" class="Symbol">{</a><a id="16247" href="Presentacion.html#16247" class="Bound">A</a> <a id="16249" href="Presentacion.html#16249" class="Bound">B</a> <a id="16251" href="Presentacion.html#16251" class="Bound">C</a> <a id="16253" class="Symbol">:</a> <a id="16255" href="Presentacion.html#8066" class="Function">Type</a><a id="16259" class="Symbol">}</a>
          <a id="16271" class="Symbol">→</a> <a id="16273" class="Symbol">(</a><a id="16274" href="Presentacion.html#16247" class="Bound">A</a> <a id="16276" class="Symbol">→</a> <a id="16278" href="Presentacion.html#16249" class="Bound">B</a> <a id="16280" class="Symbol">→</a> <a id="16282" href="Presentacion.html#16251" class="Bound">C</a><a id="16283" class="Symbol">)</a>
          <a id="16295" class="Comment">----------------</a>
          <a id="16322" class="Symbol">→</a> <a id="16324" class="Symbol">(</a><a id="16325" href="Presentacion.html#16247" class="Bound">A</a> <a id="16327" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="16329" href="Presentacion.html#16249" class="Bound">B</a> <a id="16331" class="Symbol">→</a> <a id="16333" href="Presentacion.html#16251" class="Bound">C</a><a id="16334" class="Symbol">)</a>
<a id="16336" href="Presentacion.html#16234" class="Function">currying2</a> <a id="16346" class="Symbol">=</a> <a id="16348" class="Symbol">λ</a> <a id="16350" href="Presentacion.html#16350" class="Bound">f</a> <a id="16352" class="Symbol">→</a> <a id="16354" class="Symbol">λ</a> <a id="16356" href="Presentacion.html#16356" class="Bound">ab</a> <a id="16359" class="Symbol">→</a> <a id="16361" class="Symbol">(</a><a id="16362" href="Presentacion.html#16350" class="Bound">f</a> <a id="16364" class="Symbol">(</a><a id="16365" href="Presentacion.html#13299" class="Function">∧-el</a> <a id="16370" href="Presentacion.html#16356" class="Bound">ab</a><a id="16372" class="Symbol">))</a> <a id="16375" class="Symbol">(</a><a id="16376" href="Presentacion.html#13349" class="Function">∧-er</a> <a id="16381" href="Presentacion.html#16356" class="Bound">ab</a><a id="16383" class="Symbol">)</a> 

</pre>
Podemos definir el si y solo si.

<pre class="Agda">
<a id="_⇔_"></a><a id="16435" href="Presentacion.html#16435" class="Function Operator">_⇔_</a> <a id="16439" class="Symbol">:</a> <a id="16441" class="Symbol">(</a><a id="16442" href="Presentacion.html#16442" class="Bound">A</a> <a id="16444" href="Presentacion.html#16444" class="Bound">B</a> <a id="16446" class="Symbol">:</a> <a id="16448" href="Presentacion.html#8066" class="Function">Type</a><a id="16452" class="Symbol">)</a> <a id="16454" class="Symbol">→</a> <a id="16456" href="Presentacion.html#8066" class="Function">Type</a> 
<a id="16462" href="Presentacion.html#16462" class="Bound">A</a> <a id="16464" href="Presentacion.html#16435" class="Function Operator">⇔</a> <a id="16466" href="Presentacion.html#16466" class="Bound">B</a> <a id="16468" class="Symbol">=</a> <a id="16470" class="Symbol">(</a><a id="16471" href="Presentacion.html#16462" class="Bound">A</a> <a id="16473" class="Symbol">→</a> <a id="16475" href="Presentacion.html#16466" class="Bound">B</a><a id="16476" class="Symbol">)</a> <a id="16478" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="16480" class="Symbol">(</a><a id="16481" href="Presentacion.html#16466" class="Bound">B</a> <a id="16483" class="Symbol">→</a> <a id="16485" href="Presentacion.html#16462" class="Bound">A</a><a id="16486" class="Symbol">)</a>

</pre>#### Proposición

Sean $A, B, C$ proposiciones. Entonces $A ⊃ (B ∧ C) ⇔ ((A ⊃ B) ∧ (A ⊃ C)) 

##### Demostración

Para probar una doble implicación necesitamos dar una prueba de la ida y una prueba del regreso.
Para probar la ida podemos suponer que disponemos de un término del tipo t₁ : (A → (B ∧ C)) y
debemos construir un t₂ : ((A → B) ∧ (A → C)).
Para demostrar el regreso, debemos suponer que conamos con un término t₁ : ((A → B) ∧ (A → C))
y construir un t₂ : (A → (B ∧ C))

<pre class="Agda"><a id="→-dist∧"></a><a id="16983" href="Presentacion.html#16983" class="Function">→-dist∧</a> <a id="16991" class="Symbol">:</a> <a id="16993" class="Symbol">{</a><a id="16994" href="Presentacion.html#16994" class="Bound">A</a> <a id="16996" href="Presentacion.html#16996" class="Bound">B</a> <a id="16998" href="Presentacion.html#16998" class="Bound">C</a> <a id="17000" class="Symbol">:</a> <a id="17002" href="Presentacion.html#8066" class="Function">Type</a><a id="17006" class="Symbol">}</a> <a id="17008" class="Symbol">→</a> <a id="17010" class="Symbol">(</a><a id="17011" href="Presentacion.html#16994" class="Bound">A</a> <a id="17013" class="Symbol">→</a> <a id="17015" class="Symbol">(</a><a id="17016" href="Presentacion.html#16996" class="Bound">B</a> <a id="17018" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="17020" href="Presentacion.html#16998" class="Bound">C</a><a id="17021" class="Symbol">))</a> <a id="17024" href="Presentacion.html#16435" class="Function Operator">⇔</a> <a id="17026" class="Symbol">((</a><a id="17028" href="Presentacion.html#16994" class="Bound">A</a> <a id="17030" class="Symbol">→</a> <a id="17032" href="Presentacion.html#16996" class="Bound">B</a><a id="17033" class="Symbol">)</a> <a id="17035" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="17037" class="Symbol">(</a><a id="17038" href="Presentacion.html#16994" class="Bound">A</a> <a id="17040" class="Symbol">→</a> <a id="17042" href="Presentacion.html#16998" class="Bound">C</a><a id="17043" class="Symbol">))</a>
<a id="17046" href="Presentacion.html#16983" class="Function">→-dist∧</a> <a id="17054" class="Symbol">=</a> <a id="17056" class="Symbol">(λ</a> <a id="17059" href="Presentacion.html#17059" class="Bound">t₁</a> <a id="17062" class="Symbol">→</a>                                            <a id="17107" class="Comment">-- ⊃ )</a>
                <a id="17130" class="Symbol">(λ</a> <a id="17133" href="Presentacion.html#17133" class="Bound">a</a> <a id="17135" class="Symbol">→</a> <a id="17137" href="Presentacion.html#13299" class="Function">∧-el</a> <a id="17142" class="Symbol">(</a><a id="17143" href="Presentacion.html#17059" class="Bound">t₁</a> <a id="17146" href="Presentacion.html#17133" class="Bound">a</a><a id="17147" class="Symbol">))</a> <a id="17150" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="17152" class="Symbol">λ</a> <a id="17154" href="Presentacion.html#17154" class="Bound">a</a> <a id="17156" class="Symbol">→</a> <a id="17158" href="Presentacion.html#13349" class="Function">∧-er</a> <a id="17163" class="Symbol">(</a><a id="17164" href="Presentacion.html#17059" class="Bound">t₁</a> <a id="17167" href="Presentacion.html#17154" class="Bound">a</a><a id="17168" class="Symbol">))</a> <a id="17171" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a>
          <a id="17183" class="Symbol">λ</a> <a id="17185" href="Presentacion.html#17185" class="Bound">t₁</a> <a id="17188" class="Symbol">→</a>                                             <a id="17234" class="Comment">-- ⊂ )</a>
                <a id="17257" class="Symbol">λ</a> <a id="17259" href="Presentacion.html#17259" class="Bound">a</a> <a id="17261" class="Symbol">→</a> <a id="17263" class="Symbol">(</a><a id="17264" href="Presentacion.html#13299" class="Function">∧-el</a> <a id="17269" href="Presentacion.html#17185" class="Bound">t₁</a><a id="17271" class="Symbol">)</a> <a id="17273" href="Presentacion.html#17259" class="Bound">a</a> <a id="17275" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="17277" class="Symbol">(</a><a id="17278" href="Presentacion.html#13349" class="Function">∧-er</a> <a id="17283" href="Presentacion.html#17185" class="Bound">t₁</a><a id="17285" class="Symbol">)</a> <a id="17287" href="Presentacion.html#17259" class="Bound">a</a>

</pre>
### Disjunción

La disjunción es un tipo inductivo.

<pre class="Agda"><a id="17356" class="Comment">-- Cuando se tiene algo de la forma (A B : Type) estamos diciendole a Agda que queremos</a>
<a id="17444" class="Comment">-- explicitos los tipos. Cuando se tiene algo de la forma {A B : Type} le pedimos a agda</a>
<a id="17533" class="Comment">-- que infiera los tipos.</a>

<a id="17560" class="Keyword">data</a> <a id="_∨_"></a><a id="17565" href="Presentacion.html#17565" class="Datatype Operator">_∨_</a> <a id="17569" class="Symbol">(</a><a id="17570" href="Presentacion.html#17570" class="Bound">A</a> <a id="17572" href="Presentacion.html#17572" class="Bound">B</a> <a id="17574" class="Symbol">:</a> <a id="17576" href="Presentacion.html#8066" class="Function">Type</a><a id="17580" class="Symbol">)</a> <a id="17582" class="Symbol">:</a> <a id="17584" href="Presentacion.html#8066" class="Function">Type</a> <a id="17589" class="Keyword">where</a>
  <a id="_∨_.left"></a><a id="17597" href="Presentacion.html#17597" class="InductiveConstructor">left</a>  <a id="17603" class="Symbol">:</a> <a id="17605" href="Presentacion.html#17570" class="Bound">A</a> <a id="17607" class="Symbol">→</a> <a id="17609" href="Presentacion.html#17570" class="Bound">A</a> <a id="17611" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="17613" href="Presentacion.html#17572" class="Bound">B</a>
  <a id="_∨_.right"></a><a id="17617" href="Presentacion.html#17617" class="InductiveConstructor">right</a> <a id="17623" class="Symbol">:</a> <a id="17625" href="Presentacion.html#17572" class="Bound">B</a> <a id="17627" class="Symbol">→</a> <a id="17629" href="Presentacion.html#17570" class="Bound">A</a> <a id="17631" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="17633" href="Presentacion.html#17572" class="Bound">B</a>

</pre>
Muchas veces, cuando un tipo suma está involucrado, es necesario separar por casos.
Esto se aprecia en la definición del tipo ∨, en tanto que un término de dicho tipo
en principio puede tener dos formas: dicho término pudo haber sido construido
mediante una aplicación de `left`, o mediante una aplicación de `right`. Por consiguiente,
debemos tomar en cuenta estos dos casos distintos en nuestras pruebas.

<pre class="Agda">
<a id="18058" class="Comment">--{ Principio de demostración por casos }--</a>

<a id="caseof"></a><a id="18103" href="Presentacion.html#18103" class="Function">caseof</a> <a id="18110" class="Symbol">:</a> <a id="18112" class="Symbol">{</a><a id="18113" href="Presentacion.html#18113" class="Bound">A</a> <a id="18115" href="Presentacion.html#18115" class="Bound">B</a> <a id="18117" href="Presentacion.html#18117" class="Bound">C</a> <a id="18119" class="Symbol">:</a> <a id="18121" href="Presentacion.html#8066" class="Function">Type</a><a id="18125" class="Symbol">}</a>
         <a id="18136" class="Symbol">→</a> <a id="18138" class="Symbol">(</a><a id="18139" href="Presentacion.html#18113" class="Bound">A</a> <a id="18141" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="18143" href="Presentacion.html#18115" class="Bound">B</a><a id="18144" class="Symbol">)</a>
         <a id="18155" class="Symbol">→</a> <a id="18157" class="Symbol">(</a><a id="18158" href="Presentacion.html#18113" class="Bound">A</a> <a id="18160" class="Symbol">→</a> <a id="18162" href="Presentacion.html#18117" class="Bound">C</a><a id="18163" class="Symbol">)</a>
         <a id="18174" class="Symbol">→</a> <a id="18176" class="Symbol">(</a><a id="18177" href="Presentacion.html#18115" class="Bound">B</a> <a id="18179" class="Symbol">→</a> <a id="18181" href="Presentacion.html#18117" class="Bound">C</a><a id="18182" class="Symbol">)</a>
         <a id="18193" class="Comment">----------------[∨-elim]</a>
         <a id="18227" class="Symbol">→</a> <a id="18229" href="Presentacion.html#18117" class="Bound">C</a>
 
<a id="18233" href="Presentacion.html#18103" class="Function">caseof</a> <a id="18240" class="Symbol">(</a><a id="18241" href="Presentacion.html#17597" class="InductiveConstructor">left</a> <a id="18246" href="Presentacion.html#18246" class="Bound">a∨b</a><a id="18249" class="Symbol">)</a> <a id="18251" href="Presentacion.html#18251" class="Bound">c₁</a> <a id="18254" href="Presentacion.html#18254" class="Bound">c₂</a> <a id="18257" class="Symbol">=</a> <a id="18259" href="Presentacion.html#18251" class="Bound">c₁</a> <a id="18262" href="Presentacion.html#18246" class="Bound">a∨b</a>     <a id="18270" class="Comment">-- Caso 1. Ocurre A</a>
<a id="18290" href="Presentacion.html#18103" class="Function">caseof</a> <a id="18297" class="Symbol">(</a><a id="18298" href="Presentacion.html#17617" class="InductiveConstructor">right</a> <a id="18304" href="Presentacion.html#18304" class="Bound">a∨b</a><a id="18307" class="Symbol">)</a> <a id="18309" href="Presentacion.html#18309" class="Bound">c₁</a> <a id="18312" href="Presentacion.html#18312" class="Bound">c₂</a> <a id="18315" class="Symbol">=</a> <a id="18317" href="Presentacion.html#18312" class="Bound">c₂</a> <a id="18320" href="Presentacion.html#18304" class="Bound">a∨b</a>    <a id="18327" class="Comment">-- Caso 2. Ocurre B</a>

</pre>
#### Proposición

La disjunción es conmutativa.

##### Demostración

<pre class="Agda">
<a id="∨-comm"></a><a id="18431" href="Presentacion.html#18431" class="Function">∨-comm</a> <a id="18438" class="Symbol">:</a> <a id="18440" class="Symbol">{</a><a id="18441" href="Presentacion.html#18441" class="Bound">A</a> <a id="18443" href="Presentacion.html#18443" class="Bound">B</a> <a id="18445" class="Symbol">:</a> <a id="18447" href="Presentacion.html#8066" class="Function">Type</a><a id="18451" class="Symbol">}</a> <a id="18453" class="Symbol">→</a> <a id="18455" href="Presentacion.html#18441" class="Bound">A</a> <a id="18457" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="18459" href="Presentacion.html#18443" class="Bound">B</a> <a id="18461" class="Symbol">→</a> <a id="18463" href="Presentacion.html#18443" class="Bound">B</a> <a id="18465" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="18467" href="Presentacion.html#18441" class="Bound">A</a>
<a id="18469" href="Presentacion.html#18431" class="Function">∨-comm</a> <a id="18476" class="Symbol">(</a><a id="18477" href="Presentacion.html#17597" class="InductiveConstructor">left</a> <a id="18482" href="Presentacion.html#18482" class="Bound">a∨b</a><a id="18485" class="Symbol">)</a> <a id="18487" class="Symbol">=</a> <a id="18489" href="Presentacion.html#17617" class="InductiveConstructor">right</a> <a id="18495" href="Presentacion.html#18482" class="Bound">a∨b</a>
<a id="18499" href="Presentacion.html#18431" class="Function">∨-comm</a> <a id="18506" class="Symbol">(</a><a id="18507" href="Presentacion.html#17617" class="InductiveConstructor">right</a> <a id="18513" href="Presentacion.html#18513" class="Bound">a∨b</a><a id="18516" class="Symbol">)</a> <a id="18518" class="Symbol">=</a> <a id="18520" href="Presentacion.html#17597" class="InductiveConstructor">left</a> <a id="18525" href="Presentacion.html#18513" class="Bound">a∨b</a>

</pre>#### Proposición

La disjunción distribuye sobre la conjunción.

##### Demostración

<pre class="Agda">
<a id="∨-dist∧"></a><a id="18628" href="Presentacion.html#18628" class="Function">∨-dist∧</a> <a id="18636" class="Symbol">:</a> <a id="18638" class="Symbol">{</a><a id="18639" href="Presentacion.html#18639" class="Bound">A</a> <a id="18641" href="Presentacion.html#18641" class="Bound">B</a> <a id="18643" href="Presentacion.html#18643" class="Bound">C</a> <a id="18645" class="Symbol">:</a> <a id="18647" href="Presentacion.html#8066" class="Function">Type</a><a id="18651" class="Symbol">}</a>
          <a id="18663" class="Symbol">→</a> <a id="18665" class="Symbol">(</a><a id="18666" href="Presentacion.html#18639" class="Bound">A</a> <a id="18668" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="18670" class="Symbol">(</a><a id="18671" href="Presentacion.html#18641" class="Bound">B</a> <a id="18673" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="18675" href="Presentacion.html#18643" class="Bound">C</a><a id="18676" class="Symbol">))</a>
          <a id="18689" class="Comment">-------------------</a>
          <a id="18719" class="Symbol">→</a> <a id="18721" class="Symbol">(</a><a id="18722" href="Presentacion.html#18639" class="Bound">A</a> <a id="18724" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="18726" href="Presentacion.html#18641" class="Bound">B</a><a id="18727" class="Symbol">)</a> <a id="18729" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="18731" class="Symbol">(</a><a id="18732" href="Presentacion.html#18639" class="Bound">A</a> <a id="18734" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="18736" href="Presentacion.html#18643" class="Bound">C</a><a id="18737" class="Symbol">)</a>

<a id="18740" href="Presentacion.html#18628" class="Function">∨-dist∧</a> <a id="18748" class="Symbol">(</a><a id="18749" href="Presentacion.html#17597" class="InductiveConstructor">left</a> <a id="18754" href="Presentacion.html#18754" class="Bound">a∨[b∧c]</a><a id="18761" class="Symbol">)</a> <a id="18763" class="Symbol">=</a> <a id="18765" href="Presentacion.html#17597" class="InductiveConstructor">left</a> <a id="18770" href="Presentacion.html#18754" class="Bound">a∨[b∧c]</a> <a id="18778" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="18780" href="Presentacion.html#17597" class="InductiveConstructor">left</a> <a id="18785" href="Presentacion.html#18754" class="Bound">a∨[b∧c]</a> 
<a id="18794" href="Presentacion.html#18628" class="Function">∨-dist∧</a> <a id="18802" class="Symbol">(</a><a id="18803" href="Presentacion.html#17617" class="InductiveConstructor">right</a> <a id="18809" href="Presentacion.html#18809" class="Bound">a∨[b∧c]</a><a id="18816" class="Symbol">)</a> <a id="18818" class="Symbol">=</a> <a id="18820" href="Presentacion.html#17617" class="InductiveConstructor">right</a> <a id="18826" class="Symbol">(</a><a id="18827" href="Presentacion.html#13299" class="Function">∧-el</a> <a id="18832" href="Presentacion.html#18809" class="Bound">a∨[b∧c]</a><a id="18839" class="Symbol">)</a> <a id="18841" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="18843" href="Presentacion.html#17617" class="InductiveConstructor">right</a> <a id="18849" class="Symbol">(</a><a id="18850" href="Presentacion.html#13349" class="Function">∧-er</a> <a id="18855" href="Presentacion.html#18809" class="Bound">a∨[b∧c]</a><a id="18862" class="Symbol">)</a>
</pre>
### Negación

En la lógica proposicional, una proposición falsa es aquella que no se puede demostrar.
Por lo tanto, la definimos como tal.

<pre class="Agda">
<a id="19018" class="Keyword">data</a> <a id="⊥"></a><a id="19023" href="Presentacion.html#19023" class="Datatype">⊥</a> <a id="19025" class="Symbol">:</a> <a id="19027" href="Presentacion.html#8066" class="Function">Type</a> <a id="19032" class="Keyword">where</a>

<a id="19039" class="Comment">-- su contraparte es ⊤, el tipo cuyo sólo tiene un término.</a>
<a id="19099" class="Keyword">data</a> <a id="⊤"></a><a id="19104" href="Presentacion.html#19104" class="Datatype">⊤</a> <a id="19106" class="Symbol">:</a> <a id="19108" href="Presentacion.html#8066" class="Function">Type</a> <a id="19113" class="Keyword">where</a>
  <a id="⊤.⋆"></a><a id="19121" href="Presentacion.html#19121" class="InductiveConstructor">⋆</a> <a id="19123" class="Symbol">:</a> <a id="19125" href="Presentacion.html#19104" class="Datatype">⊤</a>

</pre>
Observa que no tiene constructor alguno. Por lo tanto no hay forma de construir un término
de ⊥.

#### Principio de explosión

Si $A$ es una proposición, entonces $⊥ ⊃ A$.

#### Demostración

<pre class="Agda">
<a id="⊥-e"></a><a id="19334" href="Presentacion.html#19334" class="Function">⊥-e</a> <a id="19338" class="Symbol">:</a> <a id="19340" class="Symbol">{</a><a id="19341" href="Presentacion.html#19341" class="Bound">A</a> <a id="19343" class="Symbol">:</a> <a id="19345" href="Presentacion.html#8066" class="Function">Type</a><a id="19349" class="Symbol">}</a>
      <a id="19357" class="Symbol">→</a> <a id="19359" href="Presentacion.html#19023" class="Datatype">⊥</a>
      <a id="19367" class="Comment">-------------</a>
      <a id="19387" class="Symbol">→</a> <a id="19389" href="Presentacion.html#19341" class="Bound">A</a>

<a id="19392" href="Presentacion.html#19334" class="Function">⊥-e</a> <a id="19396" class="Symbol">()</a>
</pre>
Donde () es una "función vacía".

La negación de una proposición es un operador que recibe una proposición
y nos regresa otra proposición.

<pre class="Agda"><a id="¬"></a><a id="19552" href="Presentacion.html#19552" class="Function">¬</a> <a id="19554" class="Symbol">:</a> <a id="19556" href="Presentacion.html#8066" class="Function">Type</a> <a id="19561" class="Symbol">→</a> <a id="19563" href="Presentacion.html#8066" class="Function">Type</a>
<a id="19568" href="Presentacion.html#19552" class="Function">¬</a> <a id="19570" href="Presentacion.html#19570" class="Bound">T</a> <a id="19572" class="Symbol">=</a> <a id="19574" href="Presentacion.html#19570" class="Bound">T</a> <a id="19576" class="Symbol">→</a> <a id="19578" href="Presentacion.html#19023" class="Datatype">⊥</a>
</pre>
#### Proposición
Sean $A, B$ proposiciones. Si $A ⊃ B$ y $¬B$, entonces $¬A$.

##### Demostración

<pre class="Agda"><a id="¬impl"></a><a id="19692" href="Presentacion.html#19692" class="Function">¬impl</a> <a id="19698" class="Symbol">:</a> <a id="19700" class="Symbol">{</a><a id="19701" href="Presentacion.html#19701" class="Bound">A</a> <a id="19703" href="Presentacion.html#19703" class="Bound">B</a> <a id="19705" class="Symbol">:</a> <a id="19707" href="Presentacion.html#8066" class="Function">Type</a><a id="19711" class="Symbol">}</a>
        <a id="19721" class="Symbol">→</a> <a id="19723" class="Symbol">(</a><a id="19724" href="Presentacion.html#19701" class="Bound">A</a> <a id="19726" class="Symbol">→</a> <a id="19728" href="Presentacion.html#19703" class="Bound">B</a><a id="19729" class="Symbol">)</a>
        <a id="19739" class="Symbol">→</a> <a id="19741" href="Presentacion.html#19552" class="Function">¬</a> <a id="19743" href="Presentacion.html#19703" class="Bound">B</a>
        <a id="19753" class="Comment">-------------</a>
        <a id="19775" class="Symbol">→</a> <a id="19777" href="Presentacion.html#19552" class="Function">¬</a> <a id="19779" href="Presentacion.html#19701" class="Bound">A</a>

<a id="19782" href="Presentacion.html#19692" class="Function">¬impl</a> <a id="19788" href="Presentacion.html#19788" class="Bound">a→b</a> <a id="19792" href="Presentacion.html#19792" class="Bound">¬b</a> <a id="19795" href="Presentacion.html#19795" class="Bound">a</a> <a id="19797" class="Symbol">=</a> <a id="19799" href="Presentacion.html#19792" class="Bound">¬b</a><a id="19801" class="Symbol">(</a><a id="19802" href="Presentacion.html#15661" class="Function">→app</a> <a id="19807" href="Presentacion.html#19788" class="Bound">a→b</a> <a id="19811" href="Presentacion.html#19795" class="Bound">a</a><a id="19812" class="Symbol">)</a>

</pre>
#### Proposición
Sea $P$ una proposición. Entonces $¬(P ∧ ¬P)$.

##### Demostración

<pre class="Agda">
<a id="no-contr"></a><a id="19914" href="Presentacion.html#19914" class="Function">no-contr</a> <a id="19923" class="Symbol">:</a> <a id="19925" class="Symbol">{</a><a id="19926" href="Presentacion.html#19926" class="Bound">P</a> <a id="19928" class="Symbol">:</a> <a id="19930" href="Presentacion.html#8066" class="Function">Type</a><a id="19934" class="Symbol">}</a>
           <a id="19947" class="Comment">-----------</a>
           <a id="19970" class="Symbol">→</a> <a id="19972" href="Presentacion.html#19552" class="Function">¬</a><a id="19973" class="Symbol">(</a><a id="19974" href="Presentacion.html#19926" class="Bound">P</a> <a id="19976" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="19978" href="Presentacion.html#19552" class="Function">¬</a> <a id="19980" href="Presentacion.html#19926" class="Bound">P</a><a id="19981" class="Symbol">)</a>

<a id="19984" href="Presentacion.html#19914" class="Function">no-contr</a> <a id="19993" href="Presentacion.html#19993" class="Bound">p∧¬p</a> <a id="19998" class="Symbol">=</a> <a id="20000" href="Presentacion.html#13349" class="Function">∧-er</a> <a id="20005" href="Presentacion.html#19993" class="Bound">p∧¬p</a> <a id="20010" class="Symbol">(</a><a id="20011" href="Presentacion.html#13299" class="Function">∧-el</a> <a id="20016" href="Presentacion.html#19993" class="Bound">p∧¬p</a><a id="20020" class="Symbol">)</a>

</pre>Nuestra prueba refleja la siguiente deducción.

```haskell
 {P : Type}
 ⊢ P ∧ ¬ P
 -----------
 ⊢ ⊥
```
pero eso es justo lo que nos pide la definición de la negación.

#### Proposición

Sea $A$ una proposición. Entonces $A ⊃ ¬(¬ A)$.

##### Demostración

<pre class="Agda"><a id="¬¬I"></a><a id="20291" href="Presentacion.html#20291" class="Function">¬¬I</a> <a id="20295" class="Symbol">:</a> <a id="20297" class="Symbol">{</a><a id="20298" href="Presentacion.html#20298" class="Bound">A</a> <a id="20300" class="Symbol">:</a> <a id="20302" href="Presentacion.html#8066" class="Function">Type</a><a id="20306" class="Symbol">}</a>
      <a id="20314" class="Symbol">→</a> <a id="20316" href="Presentacion.html#20298" class="Bound">A</a>
      <a id="20324" class="Comment">-----------</a>
      <a id="20342" class="Symbol">→</a> <a id="20344" href="Presentacion.html#19552" class="Function">¬</a><a id="20345" class="Symbol">(</a><a id="20346" href="Presentacion.html#19552" class="Function">¬</a> <a id="20348" href="Presentacion.html#20298" class="Bound">A</a><a id="20349" class="Symbol">)</a>
<a id="20351" href="Presentacion.html#20291" class="Function">¬¬I</a> <a id="20355" href="Presentacion.html#20355" class="Bound">a</a> <a id="20357" class="Symbol">=</a> <a id="20359" class="Symbol">λ</a> <a id="20361" href="Presentacion.html#20361" class="Bound">¬a</a> <a id="20364" class="Symbol">→</a> <a id="20366" href="Presentacion.html#15661" class="Function">→app</a> <a id="20371" href="Presentacion.html#20361" class="Bound">¬a</a> <a id="20374" href="Presentacion.html#20355" class="Bound">a</a>
</pre>
#### Proposición

Sean $A, B$ proposiciones. Si $¬A$ y $A$ entonces $B$.

##### Demostración

<pre class="Agda"><a id="20483" class="Comment">-- Observa que por currying da igual escribir &quot;¬A&quot; y &quot;A&quot; a escribir</a>
<a id="20551" class="Comment">-- ¬A ⊃ A.</a>

<a id="¬e"></a><a id="20563" href="Presentacion.html#20563" class="Function">¬e</a> <a id="20566" class="Symbol">:</a> <a id="20568" class="Symbol">{</a><a id="20569" href="Presentacion.html#20569" class="Bound">A</a> <a id="20571" href="Presentacion.html#20571" class="Bound">B</a> <a id="20573" class="Symbol">:</a> <a id="20575" href="Presentacion.html#8066" class="Function">Type</a><a id="20579" class="Symbol">}</a>
     <a id="20586" class="Symbol">→</a> <a id="20588" href="Presentacion.html#19552" class="Function">¬</a> <a id="20590" href="Presentacion.html#20569" class="Bound">A</a>
     <a id="20597" class="Symbol">→</a> <a id="20599" href="Presentacion.html#20569" class="Bound">A</a>
     <a id="20606" class="Comment">--------------</a>
     <a id="20626" class="Symbol">→</a> <a id="20628" href="Presentacion.html#20571" class="Bound">B</a>

<a id="20631" href="Presentacion.html#20563" class="Function">¬e</a> <a id="20634" href="Presentacion.html#20634" class="Bound">¬a</a> <a id="20637" href="Presentacion.html#20637" class="Bound">a</a> <a id="20639" class="Symbol">=</a> <a id="20641" href="Presentacion.html#19334" class="Function">⊥-e</a> <a id="20645" class="Symbol">(</a><a id="20646" href="Presentacion.html#15661" class="Function">→app</a> <a id="20651" href="Presentacion.html#20634" class="Bound">¬a</a> <a id="20654" href="Presentacion.html#20637" class="Bound">a</a><a id="20655" class="Symbol">)</a>

</pre>
#### Proposición

Sean $A, B$ proposiciones. Entonces
  
  * $(¬ A ∧ ¬ B) ⊃ ¬ (A ∨ B)$
  * $¬ (A ∨ B) ⊃ (¬ A ∧ ¬ B)$
  * $(¬ A ∨ ¬ B) ⊃ ¬ (A ∧ B)$
  * $¬ (A ∧ B) ⊃ (¬ A ∨ ¬ B)$
  
##### Demostración

<pre class="Agda"><a id="¬∧¬→¬∨"></a><a id="20871" href="Presentacion.html#20871" class="Function">¬∧¬→¬∨</a> <a id="20878" class="Symbol">:</a> <a id="20880" class="Symbol">{</a><a id="20881" href="Presentacion.html#20881" class="Bound">A</a> <a id="20883" href="Presentacion.html#20883" class="Bound">B</a> <a id="20885" class="Symbol">:</a> <a id="20887" href="Presentacion.html#8066" class="Function">Type</a><a id="20891" class="Symbol">}</a>
         <a id="20902" class="Symbol">→</a> <a id="20904" href="Presentacion.html#19552" class="Function">¬</a> <a id="20906" href="Presentacion.html#20881" class="Bound">A</a> <a id="20908" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="20910" href="Presentacion.html#19552" class="Function">¬</a> <a id="20912" href="Presentacion.html#20883" class="Bound">B</a>
         <a id="20923" class="Comment">-----------</a>
         <a id="20944" class="Symbol">→</a> <a id="20946" href="Presentacion.html#19552" class="Function">¬</a> <a id="20948" class="Symbol">(</a><a id="20949" href="Presentacion.html#20881" class="Bound">A</a> <a id="20951" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="20953" href="Presentacion.html#20883" class="Bound">B</a><a id="20954" class="Symbol">)</a>

<a id="20957" href="Presentacion.html#20871" class="Function">¬∧¬→¬∨</a> <a id="20964" href="Presentacion.html#20964" class="Bound">¬a∧¬b</a> <a id="20970" href="Presentacion.html#20970" class="Bound">a∨b</a> <a id="20974" class="Symbol">=</a> <a id="20976" href="Presentacion.html#18103" class="Function">caseof</a> <a id="20983" href="Presentacion.html#20970" class="Bound">a∨b</a> <a id="20987" class="Symbol">(</a><a id="20988" href="Presentacion.html#13299" class="Function">∧-el</a> <a id="20993" href="Presentacion.html#20964" class="Bound">¬a∧¬b</a><a id="20998" class="Symbol">)</a> <a id="21000" class="Symbol">(</a><a id="21001" href="Presentacion.html#13349" class="Function">∧-er</a> <a id="21006" href="Presentacion.html#20964" class="Bound">¬a∧¬b</a><a id="21011" class="Symbol">)</a> 
<a id="¬∨→¬∧¬"></a><a id="21014" href="Presentacion.html#21014" class="Function">¬∨→¬∧¬</a> <a id="21021" class="Symbol">:</a> <a id="21023" class="Symbol">{</a><a id="21024" href="Presentacion.html#21024" class="Bound">A</a> <a id="21026" href="Presentacion.html#21026" class="Bound">B</a> <a id="21028" class="Symbol">:</a> <a id="21030" href="Presentacion.html#8066" class="Function">Type</a><a id="21034" class="Symbol">}</a>
         <a id="21045" class="Symbol">→</a> <a id="21047" href="Presentacion.html#19552" class="Function">¬</a> <a id="21049" class="Symbol">(</a><a id="21050" href="Presentacion.html#21024" class="Bound">A</a> <a id="21052" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="21054" href="Presentacion.html#21026" class="Bound">B</a><a id="21055" class="Symbol">)</a>
         <a id="21066" class="Comment">------------</a>
         <a id="21088" class="Symbol">→</a> <a id="21090" href="Presentacion.html#19552" class="Function">¬</a> <a id="21092" href="Presentacion.html#21024" class="Bound">A</a> <a id="21094" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="21096" href="Presentacion.html#19552" class="Function">¬</a> <a id="21098" href="Presentacion.html#21026" class="Bound">B</a>

<a id="21101" href="Presentacion.html#21014" class="Function">¬∨→¬∧¬</a> <a id="21108" href="Presentacion.html#21108" class="Bound">¬[a∨b]</a> <a id="21115" class="Symbol">=</a> <a id="21117" class="Symbol">(λ</a> <a id="21120" href="Presentacion.html#21120" class="Bound">a</a> <a id="21122" class="Symbol">→</a> <a id="21124" href="Presentacion.html#15661" class="Function">→app</a> <a id="21129" href="Presentacion.html#21108" class="Bound">¬[a∨b]</a> <a id="21136" class="Symbol">(</a><a id="21137" href="Presentacion.html#17597" class="InductiveConstructor">left</a> <a id="21142" href="Presentacion.html#21120" class="Bound">a</a><a id="21143" class="Symbol">))</a> <a id="21146" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="21148" class="Symbol">λ</a> <a id="21150" href="Presentacion.html#21150" class="Bound">b</a> <a id="21152" class="Symbol">→</a> <a id="21154" href="Presentacion.html#15661" class="Function">→app</a> <a id="21159" href="Presentacion.html#21108" class="Bound">¬[a∨b]</a> <a id="21166" class="Symbol">(</a><a id="21167" href="Presentacion.html#17617" class="InductiveConstructor">right</a> <a id="21173" href="Presentacion.html#21150" class="Bound">b</a><a id="21174" class="Symbol">)</a>

<a id="¬∨¬→¬∧"></a><a id="21177" href="Presentacion.html#21177" class="Function">¬∨¬→¬∧</a> <a id="21184" class="Symbol">:</a> <a id="21186" class="Symbol">{</a><a id="21187" href="Presentacion.html#21187" class="Bound">A</a> <a id="21189" href="Presentacion.html#21189" class="Bound">B</a> <a id="21191" class="Symbol">:</a> <a id="21193" href="Presentacion.html#8066" class="Function">Type</a><a id="21197" class="Symbol">}</a>
         <a id="21208" class="Symbol">→</a> <a id="21210" href="Presentacion.html#19552" class="Function">¬</a> <a id="21212" href="Presentacion.html#21187" class="Bound">A</a> <a id="21214" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="21216" href="Presentacion.html#19552" class="Function">¬</a> <a id="21218" href="Presentacion.html#21189" class="Bound">B</a>
         <a id="21229" class="Comment">------------</a>
         <a id="21251" class="Symbol">→</a> <a id="21253" href="Presentacion.html#19552" class="Function">¬</a> <a id="21255" class="Symbol">(</a><a id="21256" href="Presentacion.html#21187" class="Bound">A</a> <a id="21258" href="Presentacion.html#8060" class="Function Operator">∧</a> <a id="21260" href="Presentacion.html#21189" class="Bound">B</a><a id="21261" class="Symbol">)</a>
         
<a id="21273" href="Presentacion.html#21177" class="Function">¬∨¬→¬∧</a> <a id="21280" href="Presentacion.html#21280" class="Bound">¬a∨¬b</a> <a id="21286" href="Presentacion.html#21286" class="Bound">a∧b</a> <a id="21290" class="Symbol">=</a> <a id="21292" href="Presentacion.html#18103" class="Function">caseof</a> <a id="21299" href="Presentacion.html#21280" class="Bound">¬a∨¬b</a>
                   <a id="21324" class="Symbol">(λ</a> <a id="21327" href="Presentacion.html#21327" class="Bound">¬a</a> <a id="21330" class="Symbol">→</a>
                         <a id="21357" href="Presentacion.html#15661" class="Function">→app</a> <a id="21362" href="Presentacion.html#21327" class="Bound">¬a</a> <a id="21365" class="Symbol">(</a><a id="21366" href="Presentacion.html#13299" class="Function">∧-el</a> <a id="21371" href="Presentacion.html#21286" class="Bound">a∧b</a><a id="21374" class="Symbol">))</a>
                   <a id="21396" class="Symbol">λ</a> <a id="21398" href="Presentacion.html#21398" class="Bound">¬b</a> <a id="21401" class="Symbol">→</a>
                        <a id="21427" href="Presentacion.html#15661" class="Function">→app</a> <a id="21432" href="Presentacion.html#21398" class="Bound">¬b</a> <a id="21435" class="Symbol">(</a><a id="21436" href="Presentacion.html#13349" class="Function">∧-er</a> <a id="21441" href="Presentacion.html#21286" class="Bound">a∧b</a><a id="21444" class="Symbol">)</a>

<a id="21447" class="Comment">-- ¬∧→¬∨¬&#39; : {A B : Type}</a>
<a id="21473" class="Comment">--      → ¬ (A ∧ B)</a>
<a id="21493" class="Comment">--      -------------</a>
<a id="21515" class="Comment">--      → (¬ A ∨ ¬ B)</a>

<a id="21538" class="Comment">-- ¬∧→¬∨¬&#39; ¬a∧b = ?</a>


</pre>
### Matemáticas no constructivas

#### La Ley del Tercer Excluido y la doble negación.

El marco teórico bajo el cual trabaja Agda está basado en la lógica
intuicionista. En virtud de la equivalencia de implicación
$$
¬(A ∧ B) ⊃ ¬A ∨ ¬B
$$
con el lema del tercer excluido:
$$
A ∨ ¬A ⊃ ⊤
$$
no podemos terminar de demostrar las equivalencias de De Morgan. Si en verdad
queremos con toda nuestra alma emplear el lema del tercer excluido,
podemos introducirlo como un postulado de la siguiente forma:

  * [README.Case](http://agda.github.io/agda-stdlib/README.Case.html#1) 

<pre class="Agda">
<a id="22147" class="Keyword">postulate</a> <a id="LEM"></a><a id="22157" href="Presentacion.html#22157" class="Postulate">LEM</a> <a id="22161" class="Symbol">:</a> <a id="22163" class="Symbol">{</a><a id="22164" href="Presentacion.html#22164" class="Bound">A</a> <a id="22166" class="Symbol">:</a> <a id="22168" href="Presentacion.html#8066" class="Function">Type</a><a id="22172" class="Symbol">}</a> <a id="22174" class="Symbol">→</a>  <a id="22177" href="Presentacion.html#22164" class="Bound">A</a> <a id="22179" href="Presentacion.html#17565" class="Datatype Operator">∨</a> <a id="22181" href="Presentacion.html#19552" class="Function">¬</a> <a id="22183" href="Presentacion.html#22164" class="Bound">A</a>

<a id="lemma1"></a><a id="22186" href="Presentacion.html#22186" class="Function">lemma1</a> <a id="22193" class="Symbol">:</a> <a id="22195" class="Symbol">{</a><a id="22196" href="Presentacion.html#22196" class="Bound">A</a> <a id="22198" class="Symbol">:</a> <a id="22200" href="Presentacion.html#8066" class="Function">Type</a><a id="22204" class="Symbol">}</a> <a id="22206" class="Symbol">→</a> <a id="22208" href="Presentacion.html#19552" class="Function">¬</a> <a id="22210" class="Symbol">(</a><a id="22211" href="Presentacion.html#19552" class="Function">¬</a> <a id="22213" class="Symbol">(</a><a id="22214" href="Presentacion.html#19552" class="Function">¬</a> <a id="22216" href="Presentacion.html#22196" class="Bound">A</a><a id="22217" class="Symbol">))</a> <a id="22220" class="Symbol">→</a> <a id="22222" href="Presentacion.html#19552" class="Function">¬</a> <a id="22224" href="Presentacion.html#22196" class="Bound">A</a>
<a id="22226" href="Presentacion.html#22186" class="Function">lemma1</a> <a id="22233" href="Presentacion.html#22233" class="Bound">¬[¬¬a]</a> <a id="22240" href="Presentacion.html#22240" class="Bound">a</a> <a id="22242" class="Symbol">=</a> <a id="22244" href="Presentacion.html#15661" class="Function">→app</a> <a id="22249" href="Presentacion.html#22233" class="Bound">¬[¬¬a]</a> <a id="22256" class="Symbol">(</a><a id="22257" href="Presentacion.html#20291" class="Function">¬¬I</a> <a id="22261" href="Presentacion.html#22240" class="Bound">a</a><a id="22262" class="Symbol">)</a>

<a id="dnn"></a><a id="22265" href="Presentacion.html#22265" class="Function">dnn</a> <a id="22269" class="Symbol">:</a> <a id="22271" class="Symbol">{</a><a id="22272" href="Presentacion.html#22272" class="Bound">A</a> <a id="22274" class="Symbol">:</a> <a id="22276" href="Presentacion.html#8066" class="Function">Type</a><a id="22280" class="Symbol">}</a>
      <a id="22288" class="Symbol">→</a> <a id="22290" href="Presentacion.html#19552" class="Function">¬</a><a id="22291" class="Symbol">(</a><a id="22292" href="Presentacion.html#19552" class="Function">¬</a> <a id="22294" href="Presentacion.html#22272" class="Bound">A</a><a id="22295" class="Symbol">)</a>
      <a id="22303" class="Comment">----------</a>
      <a id="22320" class="Symbol">→</a> <a id="22322" href="Presentacion.html#22272" class="Bound">A</a>

<a id="22325" href="Presentacion.html#22265" class="Function">dnn</a> <a id="22329" class="Symbol">{</a><a id="22330" href="Presentacion.html#22330" class="Bound">A</a><a id="22331" class="Symbol">}</a> <a id="22333" href="Presentacion.html#22333" class="Bound">¬¬a</a> <a id="22337" class="Symbol">=</a> <a id="22339" href="Presentacion.html#18103" class="Function">caseof</a> <a id="22346" href="Presentacion.html#22157" class="Postulate">LEM</a>
              <a id="22364" class="Symbol">(λ</a> <a id="22367" href="Presentacion.html#22367" class="Bound">a</a> <a id="22369" class="Symbol">→</a> <a id="22371" href="Presentacion.html#22367" class="Bound">a</a><a id="22372" class="Symbol">)</a> <a id="22374" class="Comment">-- sup A</a>
              <a id="22397" class="Symbol">λ</a> <a id="22399" href="Presentacion.html#22399" class="Bound">¬a</a> <a id="22402" class="Symbol">→</a> <a id="22404" href="Presentacion.html#19334" class="Function">⊥-e</a> <a id="22408" class="Symbol">(</a><a id="22409" href="Presentacion.html#20563" class="Function">¬e</a> <a id="22412" href="Presentacion.html#22333" class="Bound">¬¬a</a> <a id="22416" href="Presentacion.html#22399" class="Bound">¬a</a><a id="22418" class="Symbol">)</a> <a id="22420" class="Comment">-- sup ¬A</a>

</pre>
¿Puedes probar la equivalencia de DeMorgan restante con estas herramientas
no constructivas?

<pre class="Agda"><a id="22538" class="Comment">-- ¬∧→¬∨¬ : {A B : Type}</a>
<a id="22563" class="Comment">--      → ¬ (A ∧ B)</a>
<a id="22583" class="Comment">--      -------------</a>
<a id="22605" class="Comment">--      → ¬ A ∨ ¬ B</a>

<a id="22626" class="Comment">-- ¬∧→¬∨¬ = ? </a>

</pre>
## Enunciados con predicados: una introducción a los tipos dependientes

En esta sección codificaremos a los números naturales en Agda y demostraremos
algunas propiedades sobre los objetos que vayamos construyendo.

#### Definición

Una familia de tipos es una función que manda términos en tipos.

##### Ejemplo

<pre class="Agda">
<a id="22970" class="Keyword">data</a> <a id="Bool"></a><a id="22975" href="Presentacion.html#22975" class="Datatype">Bool</a> <a id="22980" class="Symbol">:</a> <a id="22982" href="Presentacion.html#8066" class="Function">Type</a> <a id="22987" class="Keyword">where</a>
  <a id="Bool.true"></a><a id="22995" href="Presentacion.html#22995" class="InductiveConstructor">true</a> <a id="23000" class="Symbol">:</a> <a id="23002" href="Presentacion.html#22975" class="Datatype">Bool</a>
  <a id="Bool.false"></a><a id="23009" href="Presentacion.html#23009" class="InductiveConstructor">false</a> <a id="23015" class="Symbol">:</a> <a id="23017" href="Presentacion.html#22975" class="Datatype">Bool</a>

<a id="23023" class="Comment">-- D es una familia de tipos indizada por Bool.</a>

<a id="D"></a><a id="23072" href="Presentacion.html#23072" class="Function">D</a> <a id="23074" class="Symbol">:</a> <a id="23076" href="Presentacion.html#22975" class="Datatype">Bool</a> <a id="23081" class="Symbol">→</a> <a id="23083" href="Presentacion.html#8066" class="Function">Type</a>
<a id="23088" href="Presentacion.html#23072" class="Function">D</a> <a id="23090" href="Presentacion.html#22995" class="InductiveConstructor">true</a> <a id="23095" class="Symbol">=</a> <a id="23097" href="Presentacion.html#22975" class="Datatype">Bool</a>
<a id="23102" href="Presentacion.html#23072" class="Function">D</a> <a id="23104" href="Presentacion.html#23009" class="InductiveConstructor">false</a> <a id="23110" class="Symbol">=</a> <a id="23112" href="Presentacion.html#19023" class="Datatype">⊥</a>

<a id="23115" class="Comment">--- Los tipos dependientes nos permiten definir familias de funciones para cada Tipo</a>
<a id="23200" class="Comment">--- Esto se conoce como polimorfismo</a>

<a id="23238" class="Comment">-- Observa que esta función recibe como parámetro una familia de tipos (X : Bool → Type)</a>
<a id="23327" class="Comment">-- &quot;Para todo b : Bool, define cómo se comporta X b&quot;.</a>
<a id="if[_]_then_else_"></a><a id="23381" href="Presentacion.html#23381" class="Function Operator">if[_]_then_else_</a> <a id="23398" class="Symbol">:</a> <a id="23400" class="Symbol">(</a><a id="23401" href="Presentacion.html#23401" class="Bound">X</a> <a id="23403" class="Symbol">:</a> <a id="23405" href="Presentacion.html#22975" class="Datatype">Bool</a> <a id="23410" class="Symbol">→</a> <a id="23412" href="Presentacion.html#8066" class="Function">Type</a><a id="23416" class="Symbol">)</a>
                   <a id="23437" class="Symbol">→</a> <a id="23439" class="Symbol">(</a><a id="23440" href="Presentacion.html#23440" class="Bound">b</a> <a id="23442" class="Symbol">:</a> <a id="23444" href="Presentacion.html#22975" class="Datatype">Bool</a><a id="23448" class="Symbol">)</a>
                   <a id="23469" class="Symbol">→</a> <a id="23471" href="Presentacion.html#23401" class="Bound">X</a> <a id="23473" href="Presentacion.html#22995" class="InductiveConstructor">true</a>
                   <a id="23497" class="Symbol">→</a> <a id="23499" href="Presentacion.html#23401" class="Bound">X</a> <a id="23501" href="Presentacion.html#23009" class="InductiveConstructor">false</a>
                   <a id="23526" class="Symbol">→</a> <a id="23528" href="Presentacion.html#23401" class="Bound">X</a> <a id="23530" href="Presentacion.html#23440" class="Bound">b</a>

<a id="23533" class="Comment">-- si b es true, entonces actúa según la familia en true.</a>
<a id="23591" href="Presentacion.html#23381" class="Function Operator">if[</a> <a id="23595" href="Presentacion.html#23595" class="Bound">X</a> <a id="23597" href="Presentacion.html#23381" class="Function Operator">]</a> <a id="23599" href="Presentacion.html#22995" class="InductiveConstructor">true</a> <a id="23604" href="Presentacion.html#23381" class="Function Operator">then</a> <a id="23609" href="Presentacion.html#23609" class="Bound">x</a> <a id="23611" href="Presentacion.html#23381" class="Function Operator">else</a> <a id="23616" href="Presentacion.html#23616" class="Bound">y</a> <a id="23618" class="Symbol">=</a> <a id="23620" href="Presentacion.html#23609" class="Bound">x</a>
<a id="23622" class="Comment">-- si b es false, entonces actúa según la familia en false.</a>
<a id="23682" href="Presentacion.html#23381" class="Function Operator">if[</a> <a id="23686" href="Presentacion.html#23686" class="Bound">X</a> <a id="23688" href="Presentacion.html#23381" class="Function Operator">]</a> <a id="23690" href="Presentacion.html#23009" class="InductiveConstructor">false</a> <a id="23696" href="Presentacion.html#23381" class="Function Operator">then</a> <a id="23701" href="Presentacion.html#23701" class="Bound">x</a> <a id="23703" href="Presentacion.html#23381" class="Function Operator">else</a> <a id="23708" href="Presentacion.html#23708" class="Bound">y</a> <a id="23710" class="Symbol">=</a> <a id="23712" href="Presentacion.html#23708" class="Bound">y</a>

</pre>
$$
  \prod\limits_{b : Bool} D(b)
$$

Definimos a los números naturales como un *tipo inductivo**.

<pre class="Agda">
<a id="23829" class="Keyword">data</a> <a id="ℕ"></a><a id="23834" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="23836" class="Symbol">:</a> <a id="23838" href="Presentacion.html#8066" class="Function">Type</a> <a id="23843" class="Keyword">where</a>
  <a id="ℕ.zero"></a><a id="23851" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="23856" class="Symbol">:</a> <a id="23858" href="Presentacion.html#23834" class="Datatype">ℕ</a>
  <a id="ℕ.suc"></a><a id="23862" href="Presentacion.html#23862" class="InductiveConstructor">suc</a>  <a id="23867" class="Symbol">:</a> <a id="23869" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="23871" class="Symbol">→</a> <a id="23873" href="Presentacion.html#23834" class="Datatype">ℕ</a>

</pre>La definición es inductiva:
  * La clausula base      : `zero` es un término de ℕ
  * La clausula inductiva : si `t : ℕ` entonces `suc t : ℕ`.

Por conveniencia y eficiencia, le pedimos a Agda que utilice los símbolos con los que
estamos familiarizados para denotar a los números naturales en lugar de escribir
`suc (suc (suc … (suc zero) … ))` para denotar a un número.

<pre class="Agda">
<a id="24261" class="Symbol">{-#</a> <a id="24265" class="Keyword">BUILTIN</a> <a id="24273" class="Keyword">NATURAL</a> <a id="24281" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="24283" class="Symbol">#-}</a>

</pre>
Con la instrucción anterior, Agda se apoya en la implementación de los números
naturales con la que viene Haskell.

Ya con otro tipo más interesante, podemos jugar con nuestra función anterior

<pre class="Agda"><a id="fam"></a><a id="24495" href="Presentacion.html#24495" class="Function">fam</a> <a id="24499" class="Symbol">:</a> <a id="24501" href="Presentacion.html#22975" class="Datatype">Bool</a> <a id="24506" class="Symbol">→</a> <a id="24508" href="Presentacion.html#8066" class="Function">Type</a>
<a id="24513" href="Presentacion.html#24495" class="Function">fam</a> <a id="24517" href="Presentacion.html#22995" class="InductiveConstructor">true</a> <a id="24522" class="Symbol">=</a> <a id="24524" href="Presentacion.html#23834" class="Datatype">ℕ</a>
<a id="24526" href="Presentacion.html#24495" class="Function">fam</a> <a id="24530" href="Presentacion.html#23009" class="InductiveConstructor">false</a> <a id="24536" class="Symbol">=</a> <a id="24538" href="Presentacion.html#22975" class="Datatype">Bool</a>

<a id="fun"></a><a id="24544" href="Presentacion.html#24544" class="Function">fun</a> <a id="24548" class="Symbol">:</a> <a id="24550" class="Symbol">(</a><a id="24551" href="Presentacion.html#24551" class="Bound">b</a> <a id="24553" class="Symbol">:</a> <a id="24555" href="Presentacion.html#22975" class="Datatype">Bool</a><a id="24559" class="Symbol">)</a> <a id="24561" class="Symbol">→</a> <a id="24563" href="Presentacion.html#24495" class="Function">fam</a> <a id="24567" href="Presentacion.html#24551" class="Bound">b</a>
<a id="24569" href="Presentacion.html#24544" class="Function">fun</a> <a id="24573" href="Presentacion.html#24573" class="Bound">b</a> <a id="24575" class="Symbol">=</a> <a id="24577" href="Presentacion.html#23381" class="Function Operator">if[</a> <a id="24581" href="Presentacion.html#24495" class="Function">fam</a> <a id="24585" href="Presentacion.html#23381" class="Function Operator">]</a> <a id="24587" href="Presentacion.html#24573" class="Bound">b</a> <a id="24589" href="Presentacion.html#23381" class="Function Operator">then</a> <a id="24594" class="Number">6</a> <a id="24596" href="Presentacion.html#23381" class="Function Operator">else</a> <a id="24601" href="Presentacion.html#23009" class="InductiveConstructor">false</a>

<a id="24608" class="Comment">-- Podemos permitir que los tipos que devuelve una función no sean los mismos :D</a>
</pre>
Ya que estamos un poco más familiarizados con los tipos dependientes codifiquemos
el principio de inducción matemática en Agda para números naturales.

### Principio de Inducción

Sea $φ$ una propiedad de los números naturales. Si $φ(0)$ y $φ(n) ⊃ φ(n+1)$ entonces
$∀ k ∈ ℕ : φ(k)$.

-------------

Para codificar una propiedad de los números naturales arbitraria, podemos hacerlo
con una familia de tipos indizada sobre ℕ, de modo que `{φ : ℕ → Type}` jugará el papel
de una propiedad sobre ℕ. Luego, necesitamos construir dos términos en virtud de lo que
queremos demostrar: un término para φ(0); `φ 0`; y un término para φ(n) ⊃ φ(n+1);
`(n : ℕ) → φ n → φ (suc n)`; esto se puede leer como "$∀ n ∈ ℕ . (φ(n) ⊃ φ(n+1))$".
Nuestra meta entonces es construir un término o testigo de
`(k : ℕ) → φ n`; que se puede leer como "$∀ k ∈ ℕ . φ(k)$".

> Nota sobre la notación: [agda function-types](https://agda.readthedocs.io/en/v2.5.2/language/function-types.html)

<pre class="Agda">
<a id="ℕ-elim"></a><a id="25663" href="Presentacion.html#25663" class="Function">ℕ-elim</a> <a id="25670" class="Symbol">:</a> <a id="25672" class="Symbol">{</a><a id="25673" href="Presentacion.html#25673" class="Bound">φ</a> <a id="25675" class="Symbol">:</a> <a id="25677" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="25679" class="Symbol">→</a> <a id="25681" href="Presentacion.html#8066" class="Function">Type</a><a id="25685" class="Symbol">}</a>
         <a id="25696" class="Symbol">→</a> <a id="25698" href="Presentacion.html#25673" class="Bound">φ</a> <a id="25700" href="Presentacion.html#23851" class="InductiveConstructor">zero</a>
         <a id="25714" class="Symbol">→</a> <a id="25716" class="Symbol">((</a><a id="25718" href="Presentacion.html#25718" class="Bound">n</a> <a id="25720" class="Symbol">:</a> <a id="25722" href="Presentacion.html#23834" class="Datatype">ℕ</a><a id="25723" class="Symbol">)</a> <a id="25725" class="Symbol">→</a> <a id="25727" href="Presentacion.html#25673" class="Bound">φ</a> <a id="25729" href="Presentacion.html#25718" class="Bound">n</a> <a id="25731" class="Symbol">→</a> <a id="25733" href="Presentacion.html#25673" class="Bound">φ</a> <a id="25735" class="Symbol">(</a><a id="25736" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="25740" href="Presentacion.html#25718" class="Bound">n</a><a id="25741" class="Symbol">))</a>
         <a id="25753" class="Comment">------------------------------</a>
         <a id="25793" class="Symbol">→</a> <a id="25795" class="Symbol">∀</a> <a id="25797" class="Symbol">(</a><a id="25798" href="Presentacion.html#25798" class="Bound">k</a> <a id="25800" class="Symbol">:</a> <a id="25802" href="Presentacion.html#23834" class="Datatype">ℕ</a><a id="25803" class="Symbol">)</a> <a id="25805" class="Symbol">→</a> <a id="25807" href="Presentacion.html#25673" class="Bound">φ</a> <a id="25809" href="Presentacion.html#25798" class="Bound">k</a>                 <a id="25827" class="Comment">---- Es lo mismo que sólo escribir (k : ℕ) → φ k pero</a>
                                           <a id="25924" class="Comment">---- se ve perron jajaja (TODO Borrar esto jaja)</a>

<a id="25974" class="Comment">---- Sup. que ocurren las dos hipótesis.</a>
<a id="26015" class="Comment">---- Queremos construir un testigo de la conclusión a partir de estas hip.</a>

<a id="26091" class="Comment">-- ℕ-elim {φ} φ₀ f = h                        </a>
<a id="26138" class="Comment">--   where</a>
<a id="26149" class="Comment">--    h : (n : ℕ) → φ n</a>
<a id="26173" class="Comment">--    h n = ?</a>
<a id="26187" class="Comment">-- hacemos casos sobre n, en tanto que n ∈ ℕ implica que n es zero o es sucesor de alguien.</a>

<a id="26280" href="Presentacion.html#25663" class="Function">ℕ-elim</a> <a id="26287" class="Symbol">{</a><a id="26288" href="Presentacion.html#26288" class="Bound">φ</a><a id="26289" class="Symbol">}</a> <a id="26291" href="Presentacion.html#26291" class="Bound">φ₀</a> <a id="26294" href="Presentacion.html#26294" class="Bound">f</a> <a id="26296" class="Symbol">=</a> <a id="26298" href="Presentacion.html#26312" class="Function">h</a>
  <a id="26302" class="Keyword">where</a>
    <a id="26312" href="Presentacion.html#26312" class="Function">h</a> <a id="26314" class="Symbol">:</a> <a id="26316" class="Symbol">∀</a> <a id="26318" class="Symbol">(</a><a id="26319" href="Presentacion.html#26319" class="Bound">n</a> <a id="26321" class="Symbol">:</a> <a id="26323" href="Presentacion.html#23834" class="Datatype">ℕ</a><a id="26324" class="Symbol">)</a> <a id="26326" class="Symbol">→</a> <a id="26328" href="Presentacion.html#26288" class="Bound">φ</a> <a id="26330" href="Presentacion.html#26319" class="Bound">n</a>
    <a id="26336" href="Presentacion.html#26312" class="Function">h</a> <a id="26338" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="26343" class="Symbol">=</a> <a id="26345" href="Presentacion.html#26291" class="Bound">φ₀</a>
    <a id="26352" href="Presentacion.html#26312" class="Function">h</a> <a id="26354" class="Symbol">(</a><a id="26355" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="26359" href="Presentacion.html#26359" class="Bound">k</a><a id="26360" class="Symbol">)</a> <a id="26362" class="Symbol">=</a> <a id="26364" href="Presentacion.html#26294" class="Bound">f</a> <a id="26366" href="Presentacion.html#26359" class="Bound">k</a> <a id="26368" href="Presentacion.html#26442" class="Function">HI</a>        <a id="26378" class="Comment">----- Alternativamente, h (suc k) f k (h k)</a>
      <a id="26428" class="Keyword">where</a>
        <a id="26442" href="Presentacion.html#26442" class="Function">HI</a> <a id="26445" class="Symbol">:</a> <a id="26447" href="Presentacion.html#26288" class="Bound">φ</a> <a id="26449" href="Presentacion.html#26359" class="Bound">k</a>        <a id="26458" class="Comment">----------- la HI nos da información sobre cómo fue construida la</a>
        <a id="26532" href="Presentacion.html#26442" class="Function">HI</a> <a id="26535" class="Symbol">=</a> <a id="26537" href="Presentacion.html#26312" class="Function">h</a> <a id="26539" href="Presentacion.html#26359" class="Bound">k</a>        <a id="26548" class="Comment">----------- evidencia de φ hasta k. Recordar que φ : ℕ → Type es una fam.</a>
                        <a id="26646" class="Comment">---- Es recursivo el asunto. Para verificar h (suc k), verfica h k, y</a>
                        <a id="26740" class="Comment">---- así te vas hasta h zero, y luego te subes de regreso a h (suc k).</a>
<a id="26811" class="Comment">-- ℕ-elim {φ} φ₀ f = h                        </a>
<a id="26858" class="Comment">--   where</a>
<a id="26869" class="Comment">--    h : (n : ℕ) → φ n</a>
<a id="26893" class="Comment">--    h zero = φ₀      --- La evidencia de que φ zero ocurre es una hipótesis.</a>


    <a id="26978" class="Comment">--- La evidencia de que sabemos cómo producir una prueba para suc n está codificada</a>
    <a id="27066" class="Comment">--- en nuestra hipótesis.</a>

    <a id="27097" class="Comment">--- Agda nos pide φ (suc n). Notamos que podemos producir un término de este tipo</a>
    <a id="27183" class="Comment">--- a partir de nuestra hipótesis f. Para aplicar dicha hipótesis necesitamos</a>
    <a id="27265" class="Comment">--- un término de tipo (n₁ : ℕ) → φ n₁</a>
<a id="27304" class="Comment">--    h (suc n) = f n HI</a>
<a id="27329" class="Comment">--      where</a>
<a id="27343" class="Comment">--        HI : φ n</a>
<a id="27362" class="Comment">--        HI = h n</a>
</pre>
Una prueba más elegante:

<pre class="Agda">
<a id="Nat-elim"></a><a id="27421" href="Presentacion.html#27421" class="Function">Nat-elim</a> <a id="27430" class="Symbol">:</a> <a id="27432" class="Symbol">{</a><a id="27433" href="Presentacion.html#27433" class="Bound">φ</a> <a id="27435" class="Symbol">:</a> <a id="27437" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="27439" class="Symbol">→</a> <a id="27441" href="Presentacion.html#8066" class="Function">Type</a><a id="27445" class="Symbol">}</a>
           <a id="27458" class="Symbol">→</a> <a id="27460" href="Presentacion.html#27433" class="Bound">φ</a> <a id="27462" class="Number">0</a>
           <a id="27475" class="Symbol">→</a> <a id="27477" class="Symbol">((</a><a id="27479" href="Presentacion.html#27479" class="Bound">k</a> <a id="27481" class="Symbol">:</a> <a id="27483" href="Presentacion.html#23834" class="Datatype">ℕ</a><a id="27484" class="Symbol">)</a> <a id="27486" class="Symbol">→</a> <a id="27488" href="Presentacion.html#27433" class="Bound">φ</a> <a id="27490" href="Presentacion.html#27479" class="Bound">k</a> <a id="27492" class="Symbol">→</a> <a id="27494" href="Presentacion.html#27433" class="Bound">φ</a> <a id="27496" class="Symbol">(</a><a id="27497" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="27501" href="Presentacion.html#27479" class="Bound">k</a><a id="27502" class="Symbol">))</a>
           <a id="27516" class="Comment">--------------------------------</a>
           <a id="27560" class="Symbol">→</a> <a id="27562" class="Symbol">(</a><a id="27563" href="Presentacion.html#27563" class="Bound">n</a> <a id="27565" class="Symbol">:</a> <a id="27567" href="Presentacion.html#23834" class="Datatype">ℕ</a><a id="27568" class="Symbol">)</a> <a id="27570" class="Symbol">→</a> <a id="27572" href="Presentacion.html#27433" class="Bound">φ</a> <a id="27574" href="Presentacion.html#27563" class="Bound">n</a>


<a id="27578" href="Presentacion.html#27421" class="Function">Nat-elim</a> <a id="27587" class="Symbol">{</a><a id="27588" href="Presentacion.html#27588" class="Bound">φ</a><a id="27589" class="Symbol">}</a> <a id="27591" href="Presentacion.html#27591" class="Bound">φ₀</a> <a id="27594" href="Presentacion.html#27594" class="Bound">f</a> <a id="27596" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="27601" class="Symbol">=</a> <a id="27603" href="Presentacion.html#27591" class="Bound">φ₀</a>
<a id="27606" href="Presentacion.html#27421" class="Function">Nat-elim</a> <a id="27615" class="Symbol">{</a><a id="27616" href="Presentacion.html#27616" class="Bound">φ</a><a id="27617" class="Symbol">}</a> <a id="27619" href="Presentacion.html#27619" class="Bound">φ₀</a> <a id="27622" href="Presentacion.html#27622" class="Bound">f</a> <a id="27624" class="Symbol">(</a><a id="27625" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="27629" href="Presentacion.html#27629" class="Bound">x</a><a id="27630" class="Symbol">)</a> <a id="27632" class="Symbol">=</a> <a id="27634" href="Presentacion.html#27622" class="Bound">f</a> <a id="27636" href="Presentacion.html#27629" class="Bound">x</a> <a id="27638" class="Symbol">(</a><a id="27639" href="Presentacion.html#27421" class="Function">Nat-elim</a> <a id="27648" href="Presentacion.html#27619" class="Bound">φ₀</a> <a id="27651" href="Presentacion.html#27622" class="Bound">f</a> <a id="27653" href="Presentacion.html#27629" class="Bound">x</a><a id="27654" class="Symbol">)</a>
    
</pre>
De acuerdo con Martin Escardó, esta es la única definición recursiva en toda la teoría
de tipos de Martin Löf. Cualquier otra llamada recursiva tiene que ser propia de la
regla de eliminación del tipo inductivo.

Ahora que ya tenemos nuestro tipo de números naturales y una forma de hacer inducción
sobre estos, utilicemos estas construcciones para demostrar cosas sobre ℕ.

### La suma, el producto y el orden en ℕ

Definimos la suma de forma inductiva.

#### Definición:

La suma en ℕ se define como a continuación.

<pre class="Agda">
<a id="_+_"></a><a id="28194" href="Presentacion.html#28194" class="Function Operator">_+_</a> <a id="28198" class="Symbol">:</a> <a id="28200" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="28202" class="Symbol">→</a> <a id="28204" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="28206" class="Symbol">→</a> <a id="28208" href="Presentacion.html#23834" class="Datatype">ℕ</a>
<a id="28210" class="Comment">-- casos en m en m + n = ?</a>
<a id="28237" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="28242" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="28244" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="28249" class="Symbol">=</a> <a id="28251" href="Presentacion.html#23851" class="InductiveConstructor">zero</a>
<a id="28256" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="28261" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="28263" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28267" href="Presentacion.html#28267" class="Bound">n</a> <a id="28269" class="Symbol">=</a> <a id="28271" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28275" href="Presentacion.html#28267" class="Bound">n</a>
<a id="28277" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28281" href="Presentacion.html#28281" class="Bound">m</a> <a id="28283" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="28285" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="28290" class="Symbol">=</a> <a id="28292" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28296" href="Presentacion.html#28281" class="Bound">m</a>
<a id="28298" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28302" href="Presentacion.html#28302" class="Bound">m</a> <a id="28304" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="28306" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28310" href="Presentacion.html#28310" class="Bound">n</a> <a id="28312" class="Symbol">=</a> <a id="28314" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28318" class="Symbol">(</a><a id="28319" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28323" class="Symbol">(</a><a id="28324" href="Presentacion.html#28302" class="Bound">m</a> <a id="28326" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="28328" href="Presentacion.html#28310" class="Bound">n</a><a id="28329" class="Symbol">))</a>

<a id="_·_"></a><a id="28333" href="Presentacion.html#28333" class="Function Operator">_·_</a> <a id="28337" class="Symbol">:</a> <a id="28339" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="28341" class="Symbol">→</a> <a id="28343" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="28345" class="Symbol">→</a> <a id="28347" href="Presentacion.html#23834" class="Datatype">ℕ</a>

<a id="28350" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="28355" href="Presentacion.html#28333" class="Function Operator">·</a> <a id="28357" href="Presentacion.html#28357" class="Bound">n</a> <a id="28359" class="Symbol">=</a> <a id="28361" href="Presentacion.html#23851" class="InductiveConstructor">zero</a>
<a id="28366" class="Symbol">(</a><a id="28367" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28371" href="Presentacion.html#28371" class="Bound">m</a><a id="28372" class="Symbol">)</a> <a id="28374" href="Presentacion.html#28333" class="Function Operator">·</a> <a id="28376" href="Presentacion.html#28376" class="Bound">n</a> <a id="28378" class="Symbol">=</a> <a id="28380" class="Symbol">(</a><a id="28381" href="Presentacion.html#28371" class="Bound">m</a> <a id="28383" href="Presentacion.html#28333" class="Function Operator">·</a> <a id="28385" href="Presentacion.html#28376" class="Bound">n</a><a id="28386" class="Symbol">)</a> <a id="28388" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="28390" href="Presentacion.html#28376" class="Bound">n</a>

<a id="_≤_"></a><a id="28393" href="Presentacion.html#28393" class="Function Operator">_≤_</a> <a id="28397" class="Symbol">:</a> <a id="28399" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="28401" class="Symbol">→</a> <a id="28403" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="28405" class="Symbol">→</a> <a id="28407" href="Presentacion.html#8066" class="Function">Type</a>
<a id="28412" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="28417" href="Presentacion.html#28393" class="Function Operator">≤</a> <a id="28419" href="Presentacion.html#28419" class="Bound">y</a> <a id="28421" class="Symbol">=</a> <a id="28423" href="Presentacion.html#19104" class="Datatype">⊤</a>
<a id="28425" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28429" href="Presentacion.html#28429" class="Bound">x</a> <a id="28431" href="Presentacion.html#28393" class="Function Operator">≤</a> <a id="28433" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="28438" class="Symbol">=</a> <a id="28440" href="Presentacion.html#19023" class="Datatype">⊥</a>
<a id="28442" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28446" href="Presentacion.html#28446" class="Bound">x</a> <a id="28448" href="Presentacion.html#28393" class="Function Operator">≤</a> <a id="28450" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="28454" href="Presentacion.html#28454" class="Bound">y</a> <a id="28456" class="Symbol">=</a> <a id="28458" href="Presentacion.html#28473" class="Function">HI</a>
  <a id="28463" class="Keyword">where</a>
    <a id="28473" href="Presentacion.html#28473" class="Function">HI</a> <a id="28476" class="Symbol">:</a> <a id="28478" href="Presentacion.html#8066" class="Function">Type</a>
    <a id="28487" href="Presentacion.html#28473" class="Function">HI</a> <a id="28490" class="Symbol">=</a> <a id="28492" href="Presentacion.html#28446" class="Bound">x</a> <a id="28494" href="Presentacion.html#28393" class="Function Operator">≤</a> <a id="28496" href="Presentacion.html#28454" class="Bound">y</a>
</pre>[nat_sum]!(/Users/nicky/Working Directory/Servicio Social/PresentacionAgda/nat_sum_conm.png)

### Una introducción al tipo identidad.

La igualdad entre dos objetos matemáticos generalmente es una proposición.
Si los objetos en cuestión satisfacen nuestra definición de igualdad, entonces
podemos dar una prueba de dicha igualdad; la experiencia muestra que esto no siempre
es trivial; en otro caso, no podemos dar prueba de este hecho.

Para decidir la igualdad entre dos números naturales, por construcción necesitamos
verificar tres casos:

  * ambos son cero
  * alguno de los dos son cero
  * sus sucesores son iguales.

Entonces, dados dos números naturales, siguiendo nuestro paradigma de proposiciones como tipos,
definimos el tipo igualdad de dos números naturales.

<pre class="Agda">
<a id="_≡&#39;_"></a><a id="29287" href="Presentacion.html#29287" class="Function Operator">_≡&#39;_</a> <a id="29292" class="Symbol">:</a> <a id="29294" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="29296" class="Symbol">→</a> <a id="29298" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="29300" class="Symbol">→</a> <a id="29302" href="Presentacion.html#8066" class="Function">Type</a>
<a id="29307" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="29312" href="Presentacion.html#29287" class="Function Operator">≡&#39;</a> <a id="29315" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="29320" class="Symbol">=</a> <a id="29322" href="Presentacion.html#19104" class="Datatype">⊤</a>
<a id="29324" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="29329" href="Presentacion.html#29287" class="Function Operator">≡&#39;</a> <a id="29332" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="29336" href="Presentacion.html#29336" class="Bound">b</a> <a id="29338" class="Symbol">=</a> <a id="29340" href="Presentacion.html#19023" class="Datatype">⊥</a> <a id="29342" class="Comment">-- el cero no es sucesor de nadie</a>
<a id="29376" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="29380" href="Presentacion.html#29380" class="Bound">a</a> <a id="29382" href="Presentacion.html#29287" class="Function Operator">≡&#39;</a> <a id="29385" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="29390" class="Symbol">=</a> <a id="29392" href="Presentacion.html#19023" class="Datatype">⊥</a> <a id="29394" class="Comment">-- no tenemos reflexividad todavia. Mismo caso que el anterior.</a>
<a id="29458" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="29462" href="Presentacion.html#29462" class="Bound">a</a> <a id="29464" href="Presentacion.html#29287" class="Function Operator">≡&#39;</a> <a id="29467" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="29471" href="Presentacion.html#29471" class="Bound">b</a> <a id="29473" class="Symbol">=</a> <a id="29475" href="Presentacion.html#29462" class="Bound">a</a> <a id="29477" href="Presentacion.html#29287" class="Function Operator">≡&#39;</a> <a id="29480" href="Presentacion.html#29471" class="Bound">b</a> <a id="29482" class="Comment">-- si sus sucesores son iguales, entonces inductivamente decidimos.</a>

</pre>
Existe una forma más general de definir la igualdad para cualesquier tipo, y es mediante
el tipo identidad. El razonamiento básico detrás de la definición es la siguiente:

> Bajo el paradigma de Tipos como Proposiciones, como ya se discutió antes, tiene sentido
pensar en la igualdad como un tipo más. Sin embargo, queremos definir la igualdad para
cualquier tipo. ¿Cómo definimos este tipo? La información básica para decidir la igualdad
entre dos objetos es la siguiente: necesitamos la clase de objetos con los que estamos lidiando,
esto es el tipo de los objetos a comparar, a saber `T`, y necesitamos dos objetos a comparar,
esto es, `x : T` y `y : T`. Dada esta información, el tipo igualdad `x = y` es un tipo que
depende de los términos `x` y `y`. Por lo tanto `x = y` debe ser un tipo dependiente.
Si `p : x = y`, entonces es porque `p` es testigo de la igualdad; en otras palabras,
`p` es una identificación de `x` y de `y`. Si `p, q : x = y`, entonces debemos poder formar
también el tipo `p = q`. De esta forma, podemos emplear a los tipos para decir cosas sobre
la igualdad (¿será que dos identificaciones también pueden identificarse entre si?, ¡pensar en
homotopía!). Finalmente, la propiedad fundamental que satisfacen todas las nociones de igualdad
es una de reflexividad. Se codifica al tipo identidad entonces como un tipo inductivo
dependiente con un constructor que debe testificar la reflexividad, con el propósito de dotar
de estructura inductiva y de tipo con el fin de hacer más rica la discusión sobre la igualdad
en la teoría.

Aunque la discusión dada en esta exposición es quizás un poco larga, el tema de igualdad
es uno muy rico en contenido y discusión dentro de la teoría homotópica de tipos. Se hace
la cordial invitación a leer más sobre el tema en las referencias.

<pre class="Agda"><a id="31367" class="Comment">-- Dados un tipo T, para cada dos x , y : T</a>
<a id="31411" class="Comment">-- tenemos un tipo x ≡ y llamado tipo identidad de x a y.</a>
<a id="31469" class="Keyword">data</a> <a id="_≡_"></a><a id="31474" href="Presentacion.html#31474" class="Datatype Operator">_≡_</a> <a id="31478" class="Symbol">{</a><a id="31479" href="Presentacion.html#31479" class="Bound">T</a> <a id="31481" class="Symbol">:</a> <a id="31483" href="Presentacion.html#8066" class="Function">Type</a><a id="31487" class="Symbol">}</a> <a id="31489" class="Symbol">:</a> <a id="31491" href="Presentacion.html#31479" class="Bound">T</a> <a id="31493" class="Symbol">→</a> <a id="31495" href="Presentacion.html#31479" class="Bound">T</a> <a id="31497" class="Symbol">→</a> <a id="31499" href="Presentacion.html#8066" class="Function">Type</a> <a id="31504" class="Keyword">where</a>
  <a id="_≡_.refl"></a><a id="31512" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="31517" class="Symbol">:</a> <a id="31519" class="Symbol">(</a><a id="31520" href="Presentacion.html#31520" class="Bound">x</a> <a id="31522" class="Symbol">:</a> <a id="31524" href="Presentacion.html#31479" class="Bound">T</a><a id="31525" class="Symbol">)</a> <a id="31527" class="Symbol">→</a> <a id="31529" href="Presentacion.html#31520" class="Bound">x</a> <a id="31531" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="31533" href="Presentacion.html#31520" class="Bound">x</a>

<a id="31536" class="Comment">-- x ≡ y es la proposición &quot;x = y según T&quot;, y para cada x tenemos una prueba de que x es</a>
<a id="31625" class="Comment">-- igual a x según T.</a>
</pre>Probemos la reflexividad de ≡.

#### Proposición
≡ es transitiva y simétrica.

##### Demostración

<pre class="Agda">
<a id="≡-sym"></a><a id="31759" href="Presentacion.html#31759" class="Function">≡-sym</a> <a id="31765" class="Symbol">:</a> <a id="31767" class="Symbol">∀</a> <a id="31769" class="Symbol">{</a><a id="31770" href="Presentacion.html#31770" class="Bound">T</a> <a id="31772" class="Symbol">:</a> <a id="31774" href="Presentacion.html#8066" class="Function">Type</a><a id="31778" class="Symbol">}</a> <a id="31780" class="Symbol">{</a><a id="31781" href="Presentacion.html#31781" class="Bound">n</a> <a id="31783" href="Presentacion.html#31783" class="Bound">m</a> <a id="31785" class="Symbol">:</a> <a id="31787" href="Presentacion.html#31770" class="Bound">T</a><a id="31788" class="Symbol">}</a>
        <a id="31798" class="Symbol">→</a> <a id="31800" href="Presentacion.html#31781" class="Bound">n</a> <a id="31802" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="31804" href="Presentacion.html#31783" class="Bound">m</a>
        <a id="31814" class="Comment">-----------</a>
        <a id="31834" class="Symbol">→</a> <a id="31836" href="Presentacion.html#31783" class="Bound">m</a> <a id="31838" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="31840" href="Presentacion.html#31781" class="Bound">n</a>

<a id="31843" class="Comment">-- n ≡ m fue construido como `refl n`</a>
<a id="31881" class="Comment">-- para construir m ≡ n basta entonces hacer lo mismo, en tanto que n ≡ m.</a>
<a id="31956" class="Comment">-- es decir, tanto m y n están identificados internamente en T.</a>
<a id="32020" href="Presentacion.html#31759" class="Function">≡-sym</a> <a id="32026" class="Symbol">(</a><a id="32027" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="32032" href="Presentacion.html#32032" class="Bound">n</a><a id="32033" class="Symbol">)</a> <a id="32035" class="Symbol">=</a> <a id="32037" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="32042" href="Presentacion.html#32032" class="Bound">n</a>

<a id="≡-trans"></a><a id="32045" href="Presentacion.html#32045" class="Function">≡-trans</a> <a id="32053" class="Symbol">:</a> <a id="32055" class="Symbol">∀</a> <a id="32057" class="Symbol">{</a><a id="32058" href="Presentacion.html#32058" class="Bound">A</a> <a id="32060" class="Symbol">:</a> <a id="32062" href="Presentacion.html#8066" class="Function">Type</a><a id="32066" class="Symbol">}</a> <a id="32068" class="Symbol">{</a><a id="32069" href="Presentacion.html#32069" class="Bound">x</a> <a id="32071" href="Presentacion.html#32071" class="Bound">y</a> <a id="32073" href="Presentacion.html#32073" class="Bound">z</a> <a id="32075" class="Symbol">:</a> <a id="32077" href="Presentacion.html#32058" class="Bound">A</a><a id="32078" class="Symbol">}</a>
          <a id="32090" class="Symbol">→</a> <a id="32092" href="Presentacion.html#32069" class="Bound">x</a> <a id="32094" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="32096" href="Presentacion.html#32071" class="Bound">y</a>
          <a id="32108" class="Symbol">→</a> <a id="32110" href="Presentacion.html#32071" class="Bound">y</a> <a id="32112" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="32114" href="Presentacion.html#32073" class="Bound">z</a>
          <a id="32126" class="Comment">-------------------------</a>
          <a id="32162" class="Symbol">→</a> <a id="32164" href="Presentacion.html#32069" class="Bound">x</a> <a id="32166" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="32168" href="Presentacion.html#32073" class="Bound">z</a>

<a id="32171" class="Comment">-- como x ≡ y, y por hipótesis y ≡ z, entonces x y z deben estar</a>
<a id="32236" class="Comment">-- también identificados en x ≡ y</a>
<a id="32270" class="Comment">-- ≡-trans x≡y (refl y) = x≡y</a>
<a id="32300" href="Presentacion.html#32045" class="Function">≡-trans</a> <a id="32308" class="Symbol">(</a><a id="32309" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="32314" href="Presentacion.html#32314" class="Bound">x</a><a id="32315" class="Symbol">)</a> <a id="32317" class="Symbol">(</a><a id="32318" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="32323" href="Presentacion.html#32323" class="Bound">y</a><a id="32324" class="Symbol">)</a> <a id="32326" class="Symbol">=</a> <a id="32328" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="32333" href="Presentacion.html#32314" class="Bound">x</a>
</pre>Regresando a nuestras definiciones de suma, producto y orden; ya con
el tipo identidad y los tipos dependientes podemos demostrar propiedades sobre
estas operaciones.

#### Lema:
  * ∀ A B : Type . ∀ f : A → B . ∀ x y : T . x ≡ y ⇒ f x ≡ f y 
  * ∀ n ∈ ℕ . n + 0 = n
  * ∀ n ∈ ℕ . 0 + n = n
  * ∀ n, m ∈ ℕ . n + suc m = suc (m + n)

##### Demostración:

<pre class="Agda">
<a id="cong"></a><a id="32702" href="Presentacion.html#32702" class="Function">cong</a> <a id="32707" class="Symbol">:</a> <a id="32709" class="Symbol">∀</a> <a id="32711" class="Symbol">{</a><a id="32712" href="Presentacion.html#32712" class="Bound">A</a> <a id="32714" href="Presentacion.html#32714" class="Bound">B</a> <a id="32716" class="Symbol">:</a> <a id="32718" href="Presentacion.html#8066" class="Function">Type</a><a id="32722" class="Symbol">}</a> <a id="32724" class="Symbol">(</a><a id="32725" href="Presentacion.html#32725" class="Bound">f</a> <a id="32727" class="Symbol">:</a> <a id="32729" href="Presentacion.html#32712" class="Bound">A</a> <a id="32731" class="Symbol">→</a> <a id="32733" href="Presentacion.html#32714" class="Bound">B</a><a id="32734" class="Symbol">)</a> <a id="32736" class="Symbol">{</a><a id="32737" href="Presentacion.html#32737" class="Bound">x</a> <a id="32739" href="Presentacion.html#32739" class="Bound">y</a> <a id="32741" class="Symbol">:</a> <a id="32743" href="Presentacion.html#32712" class="Bound">A</a><a id="32744" class="Symbol">}</a>
       <a id="32753" class="Symbol">→</a> <a id="32755" href="Presentacion.html#32737" class="Bound">x</a> <a id="32757" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="32759" href="Presentacion.html#32739" class="Bound">y</a>
       <a id="32768" class="Comment">--------</a>
       <a id="32784" class="Symbol">→</a> <a id="32786" href="Presentacion.html#32725" class="Bound">f</a> <a id="32788" href="Presentacion.html#32737" class="Bound">x</a> <a id="32790" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="32792" href="Presentacion.html#32725" class="Bound">f</a> <a id="32794" href="Presentacion.html#32739" class="Bound">y</a>
<a id="32796" href="Presentacion.html#32702" class="Function">cong</a> <a id="32801" href="Presentacion.html#32801" class="Bound">f</a> <a id="32803" class="Symbol">(</a><a id="32804" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="32809" href="Presentacion.html#32809" class="Bound">x</a><a id="32810" class="Symbol">)</a> <a id="32812" class="Symbol">=</a> <a id="32814" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="32819" class="Symbol">(</a><a id="32820" href="Presentacion.html#32801" class="Bound">f</a> <a id="32822" href="Presentacion.html#32809" class="Bound">x</a><a id="32823" class="Symbol">)</a>

<a id="zero+n-=-n"></a><a id="32826" href="Presentacion.html#32826" class="Function">zero+n-=-n</a> <a id="32837" class="Symbol">:</a> <a id="32839" class="Symbol">∀</a> <a id="32841" class="Symbol">(</a><a id="32842" href="Presentacion.html#32842" class="Bound">n</a> <a id="32844" class="Symbol">:</a> <a id="32846" href="Presentacion.html#23834" class="Datatype">ℕ</a><a id="32847" class="Symbol">)</a> <a id="32849" class="Symbol">→</a> <a id="32851" class="Symbol">(</a><a id="32852" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="32857" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="32859" href="Presentacion.html#32842" class="Bound">n</a><a id="32860" class="Symbol">)</a> <a id="32862" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="32864" href="Presentacion.html#32842" class="Bound">n</a>
<a id="32866" href="Presentacion.html#32826" class="Function">zero+n-=-n</a> <a id="32877" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="32882" class="Symbol">=</a> <a id="32884" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="32889" href="Presentacion.html#23851" class="InductiveConstructor">zero</a>
<a id="32894" href="Presentacion.html#32826" class="Function">zero+n-=-n</a> <a id="32905" class="Symbol">(</a><a id="32906" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="32910" href="Presentacion.html#32910" class="Bound">n</a><a id="32911" class="Symbol">)</a> <a id="32913" class="Symbol">=</a> <a id="32915" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="32920" class="Symbol">(</a><a id="32921" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="32925" href="Presentacion.html#32910" class="Bound">n</a><a id="32926" class="Symbol">)</a>

<a id="n+zero-=-n"></a><a id="32929" href="Presentacion.html#32929" class="Function">n+zero-=-n</a> <a id="32940" class="Symbol">:</a> <a id="32942" class="Symbol">∀</a> <a id="32944" class="Symbol">(</a><a id="32945" href="Presentacion.html#32945" class="Bound">n</a> <a id="32947" class="Symbol">:</a> <a id="32949" href="Presentacion.html#23834" class="Datatype">ℕ</a><a id="32950" class="Symbol">)</a> <a id="32952" class="Symbol">→</a> <a id="32954" class="Symbol">(</a><a id="32955" href="Presentacion.html#32945" class="Bound">n</a> <a id="32957" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="32959" href="Presentacion.html#23851" class="InductiveConstructor">zero</a><a id="32963" class="Symbol">)</a> <a id="32965" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="32967" href="Presentacion.html#32945" class="Bound">n</a>
<a id="32969" href="Presentacion.html#32929" class="Function">n+zero-=-n</a> <a id="32980" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="32985" class="Symbol">=</a> <a id="32987" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="32992" href="Presentacion.html#23851" class="InductiveConstructor">zero</a>
<a id="32997" href="Presentacion.html#32929" class="Function">n+zero-=-n</a> <a id="33008" class="Symbol">(</a><a id="33009" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33013" href="Presentacion.html#33013" class="Bound">n</a><a id="33014" class="Symbol">)</a> <a id="33016" class="Symbol">=</a> <a id="33018" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="33023" class="Symbol">(</a><a id="33024" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33028" href="Presentacion.html#33013" class="Bound">n</a><a id="33029" class="Symbol">)</a>

<a id="33032" class="Comment">-- Doble inducción sobre n y m :D</a>

<a id="+-suc"></a><a id="33067" href="Presentacion.html#33067" class="Function">+-suc</a> <a id="33073" class="Symbol">:</a> <a id="33075" class="Symbol">∀</a> <a id="33077" class="Symbol">(</a><a id="33078" href="Presentacion.html#33078" class="Bound">n</a> <a id="33080" href="Presentacion.html#33080" class="Bound">m</a> <a id="33082" class="Symbol">:</a> <a id="33084" href="Presentacion.html#23834" class="Datatype">ℕ</a><a id="33085" class="Symbol">)</a> <a id="33087" class="Symbol">→</a> <a id="33089" class="Symbol">(</a><a id="33090" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33094" href="Presentacion.html#33080" class="Bound">m</a> <a id="33096" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33098" href="Presentacion.html#33078" class="Bound">n</a><a id="33099" class="Symbol">)</a> <a id="33101" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="33103" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33107" class="Symbol">(</a><a id="33108" href="Presentacion.html#33080" class="Bound">m</a> <a id="33110" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33112" href="Presentacion.html#33078" class="Bound">n</a><a id="33113" class="Symbol">)</a>

<a id="33116" href="Presentacion.html#33067" class="Function">+-suc</a> <a id="33122" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="33127" href="Presentacion.html#33127" class="Bound">m</a> <a id="33129" class="Symbol">=</a> <a id="33131" href="Presentacion.html#32702" class="Function">cong</a> <a id="33136" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33140" class="Symbol">(</a><a id="33141" href="Presentacion.html#31759" class="Function">≡-sym</a> <a id="33147" class="Symbol">(</a><a id="33148" href="Presentacion.html#32929" class="Function">n+zero-=-n</a> <a id="33159" href="Presentacion.html#33127" class="Bound">m</a><a id="33160" class="Symbol">))</a>
<a id="33163" href="Presentacion.html#33067" class="Function">+-suc</a> <a id="33169" class="Symbol">(</a><a id="33170" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33174" href="Presentacion.html#33174" class="Bound">n</a><a id="33175" class="Symbol">)</a> <a id="33177" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="33182" class="Symbol">=</a> <a id="33184" href="Presentacion.html#32702" class="Function">cong</a> <a id="33189" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33193" class="Symbol">(</a><a id="33194" href="Presentacion.html#32702" class="Function">cong</a> <a id="33199" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33203" class="Symbol">(</a><a id="33204" href="Presentacion.html#32826" class="Function">zero+n-=-n</a> <a id="33215" href="Presentacion.html#33174" class="Bound">n</a><a id="33216" class="Symbol">))</a>
<a id="33219" href="Presentacion.html#33067" class="Function">+-suc</a> <a id="33225" class="Symbol">(</a><a id="33226" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33230" href="Presentacion.html#33230" class="Bound">n</a><a id="33231" class="Symbol">)</a> <a id="33233" class="Symbol">(</a><a id="33234" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33238" href="Presentacion.html#33238" class="Bound">m</a><a id="33239" class="Symbol">)</a> <a id="33241" class="Symbol">=</a> <a id="33243" href="Presentacion.html#32702" class="Function">cong</a> <a id="33248" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33252" class="Symbol">(</a><a id="33253" href="Presentacion.html#32702" class="Function">cong</a> <a id="33258" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33262" href="Presentacion.html#33278" class="Function">HI</a><a id="33264" class="Symbol">)</a>
  <a id="33268" class="Keyword">where</a>
    <a id="33278" href="Presentacion.html#33278" class="Function">HI</a> <a id="33281" class="Symbol">:</a> <a id="33283" class="Symbol">(</a><a id="33284" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33288" href="Presentacion.html#33238" class="Bound">m</a> <a id="33290" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33292" href="Presentacion.html#33230" class="Bound">n</a><a id="33293" class="Symbol">)</a> <a id="33295" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="33297" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33301" class="Symbol">(</a><a id="33302" href="Presentacion.html#33238" class="Bound">m</a> <a id="33304" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33306" href="Presentacion.html#33230" class="Bound">n</a><a id="33307" class="Symbol">)</a>
    <a id="33313" href="Presentacion.html#33278" class="Function">HI</a> <a id="33316" class="Symbol">=</a> <a id="33318" href="Presentacion.html#33067" class="Function">+-suc</a> <a id="33324" href="Presentacion.html#33230" class="Bound">n</a> <a id="33326" href="Presentacion.html#33238" class="Bound">m</a>
              
</pre>
#### Proposición:
La suma en ℕ es conmutativa.

##### Demostración

<pre class="Agda">
<a id="+-conm"></a><a id="33425" href="Presentacion.html#33425" class="Function">+-conm</a> <a id="33432" class="Symbol">:</a> <a id="33434" class="Symbol">∀</a> <a id="33436" class="Symbol">(</a><a id="33437" href="Presentacion.html#33437" class="Bound">x</a> <a id="33439" href="Presentacion.html#33439" class="Bound">y</a> <a id="33441" class="Symbol">:</a> <a id="33443" href="Presentacion.html#23834" class="Datatype">ℕ</a><a id="33444" class="Symbol">)</a> <a id="33446" class="Symbol">→</a> <a id="33448" class="Symbol">(</a><a id="33449" href="Presentacion.html#33437" class="Bound">x</a> <a id="33451" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33453" href="Presentacion.html#33439" class="Bound">y</a><a id="33454" class="Symbol">)</a> <a id="33456" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="33458" class="Symbol">(</a><a id="33459" href="Presentacion.html#33439" class="Bound">y</a> <a id="33461" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33463" href="Presentacion.html#33437" class="Bound">x</a><a id="33464" class="Symbol">)</a>

<a id="33467" href="Presentacion.html#33425" class="Function">+-conm</a> <a id="33474" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="33479" href="Presentacion.html#33479" class="Bound">y</a> <a id="33481" class="Symbol">=</a> <a id="33483" href="Presentacion.html#31759" class="Function">≡-sym</a> <a id="33489" href="Presentacion.html#33646" class="Function">AF4</a>
  <a id="33495" class="Keyword">where</a>
    <a id="33505" href="Presentacion.html#33505" class="Function">AF1</a> <a id="33509" class="Symbol">:</a> <a id="33511" class="Symbol">(</a><a id="33512" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="33517" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33519" href="Presentacion.html#33479" class="Bound">y</a><a id="33520" class="Symbol">)</a> <a id="33522" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="33524" href="Presentacion.html#33479" class="Bound">y</a>
    <a id="33530" href="Presentacion.html#33505" class="Function">AF1</a> <a id="33534" class="Symbol">=</a> <a id="33536" href="Presentacion.html#32826" class="Function">zero+n-=-n</a> <a id="33547" href="Presentacion.html#33479" class="Bound">y</a>
    <a id="33553" href="Presentacion.html#33553" class="Function">AF2</a> <a id="33557" class="Symbol">:</a> <a id="33559" class="Symbol">(</a><a id="33560" href="Presentacion.html#33479" class="Bound">y</a> <a id="33562" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33564" href="Presentacion.html#23851" class="InductiveConstructor">zero</a><a id="33568" class="Symbol">)</a> <a id="33570" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="33572" href="Presentacion.html#33479" class="Bound">y</a>
    <a id="33578" href="Presentacion.html#33553" class="Function">AF2</a> <a id="33582" class="Symbol">=</a> <a id="33584" href="Presentacion.html#32929" class="Function">n+zero-=-n</a> <a id="33595" href="Presentacion.html#33479" class="Bound">y</a>
    <a id="33601" href="Presentacion.html#33601" class="Function">AF3</a> <a id="33605" class="Symbol">:</a> <a id="33607" href="Presentacion.html#33479" class="Bound">y</a> <a id="33609" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="33611" class="Symbol">(</a><a id="33612" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="33617" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33619" href="Presentacion.html#33479" class="Bound">y</a><a id="33620" class="Symbol">)</a>
    <a id="33626" href="Presentacion.html#33601" class="Function">AF3</a> <a id="33630" class="Symbol">=</a> <a id="33632" href="Presentacion.html#31759" class="Function">≡-sym</a> <a id="33638" href="Presentacion.html#33505" class="Function">AF1</a>
    <a id="33646" href="Presentacion.html#33646" class="Function">AF4</a> <a id="33650" class="Symbol">:</a> <a id="33652" class="Symbol">(</a><a id="33653" href="Presentacion.html#33479" class="Bound">y</a> <a id="33655" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33657" href="Presentacion.html#23851" class="InductiveConstructor">zero</a><a id="33661" class="Symbol">)</a> <a id="33663" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="33665" class="Symbol">(</a><a id="33666" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="33671" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33673" href="Presentacion.html#33479" class="Bound">y</a><a id="33674" class="Symbol">)</a>
    <a id="33680" href="Presentacion.html#33646" class="Function">AF4</a> <a id="33684" class="Symbol">=</a> <a id="33686" href="Presentacion.html#32045" class="Function">≡-trans</a> <a id="33694" href="Presentacion.html#33553" class="Function">AF2</a> <a id="33698" href="Presentacion.html#33601" class="Function">AF3</a>
<a id="33702" href="Presentacion.html#33425" class="Function">+-conm</a> <a id="33709" class="Symbol">(</a><a id="33710" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33714" href="Presentacion.html#33714" class="Bound">x</a><a id="33715" class="Symbol">)</a> <a id="33717" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="33722" class="Symbol">=</a> <a id="33724" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="33729" class="Symbol">(</a><a id="33730" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33734" href="Presentacion.html#33714" class="Bound">x</a><a id="33735" class="Symbol">)</a>
<a id="33737" href="Presentacion.html#33425" class="Function">+-conm</a> <a id="33744" class="Symbol">(</a><a id="33745" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33749" href="Presentacion.html#33749" class="Bound">x</a><a id="33750" class="Symbol">)</a> <a id="33752" class="Symbol">(</a><a id="33753" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33757" href="Presentacion.html#33757" class="Bound">y</a><a id="33758" class="Symbol">)</a> <a id="33760" class="Symbol">=</a> <a id="33762" href="Presentacion.html#32702" class="Function">cong</a> <a id="33767" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33771" class="Symbol">(</a><a id="33772" href="Presentacion.html#32702" class="Function">cong</a> <a id="33777" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="33781" href="Presentacion.html#33797" class="Function">HI</a><a id="33783" class="Symbol">)</a>
  <a id="33787" class="Keyword">where</a>
    <a id="33797" href="Presentacion.html#33797" class="Function">HI</a> <a id="33800" class="Symbol">:</a> <a id="33802" class="Symbol">(</a><a id="33803" href="Presentacion.html#33749" class="Bound">x</a> <a id="33805" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33807" href="Presentacion.html#33757" class="Bound">y</a><a id="33808" class="Symbol">)</a> <a id="33810" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="33812" class="Symbol">(</a><a id="33813" href="Presentacion.html#33757" class="Bound">y</a> <a id="33815" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="33817" href="Presentacion.html#33749" class="Bound">x</a><a id="33818" class="Symbol">)</a> 
    <a id="33825" href="Presentacion.html#33797" class="Function">HI</a> <a id="33828" class="Symbol">=</a> <a id="33830" href="Presentacion.html#33425" class="Function">+-conm</a> <a id="33837" href="Presentacion.html#33749" class="Bound">x</a> <a id="33839" href="Presentacion.html#33757" class="Bound">y</a>

</pre>
#### Proposición

x ≤ y ⇔ ∃ k : ℕ . x + k = y

##### Demostración

<pre class="Agda"><a id="33922" class="Keyword">open</a> <a id="33927" class="Keyword">import</a> <a id="33934" href="Agda.Builtin.Sigma.html" class="Module">Agda.Builtin.Sigma</a>

<a id="-Σ"></a><a id="33954" href="Presentacion.html#33954" class="Function">-Σ</a> <a id="33957" class="Symbol">=</a> <a id="33959" href="Agda.Builtin.Sigma.html#148" class="Record">Σ</a>
<a id="33961" class="Keyword">infix</a> <a id="33967" class="Number">2</a> <a id="33969" href="Presentacion.html#33954" class="Function">-Σ</a>
<a id="33972" class="Keyword">syntax</a> <a id="33979" href="Presentacion.html#33954" class="Function">-Σ</a> <a id="33982" class="Bound">A</a> <a id="33984" class="Symbol">(λ</a> <a id="33987" class="Bound">x</a> <a id="33989" class="Symbol">→</a> <a id="33991" class="Bound">B</a><a id="33992" class="Symbol">)</a> <a id="33994" class="Symbol">=</a> <a id="33996" class="Function">∃</a> <a id="33998" class="Bound">x</a> <a id="34000" class="Function">∈</a> <a id="34002" class="Bound">A</a> <a id="34004" class="Function">,</a> <a id="34006" class="Bound">B</a> 

<a id="_~_"></a><a id="34010" href="Presentacion.html#34010" class="Function Operator">_~_</a> <a id="34014" class="Symbol">:</a> <a id="34016" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="34018" class="Symbol">→</a> <a id="34020" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="34022" class="Symbol">→</a> <a id="34024" href="Presentacion.html#8066" class="Function">Type</a>

<a id="34030" href="Presentacion.html#34030" class="Bound">a</a> <a id="34032" href="Presentacion.html#34010" class="Function Operator">~</a> <a id="34034" href="Presentacion.html#34034" class="Bound">b</a> <a id="34036" class="Symbol">=</a> <a id="34038" href="Presentacion.html#33954" class="Function">∃</a> <a id="34040" href="Presentacion.html#34040" class="Bound">k</a> <a id="34042" href="Presentacion.html#33954" class="Function">∈</a> <a id="34044" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="34046" href="Presentacion.html#33954" class="Function">,</a> <a id="34048" class="Symbol">(</a><a id="34049" href="Presentacion.html#34030" class="Bound">a</a> <a id="34051" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="34053" href="Presentacion.html#34040" class="Bound">k</a><a id="34054" class="Symbol">)</a> <a id="34056" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="34058" href="Presentacion.html#34034" class="Bound">b</a> 

<a id="~-es-≤"></a><a id="34062" href="Presentacion.html#34062" class="Function">~-es-≤</a> <a id="34069" class="Symbol">:</a> <a id="34071" class="Symbol">∀</a> <a id="34073" class="Symbol">(</a><a id="34074" href="Presentacion.html#34074" class="Bound">a</a> <a id="34076" href="Presentacion.html#34076" class="Bound">b</a> <a id="34078" class="Symbol">:</a> <a id="34080" href="Presentacion.html#23834" class="Datatype">ℕ</a><a id="34081" class="Symbol">)</a>
         <a id="34092" class="Symbol">→</a> <a id="34094" href="Presentacion.html#34074" class="Bound">a</a> <a id="34096" href="Presentacion.html#28393" class="Function Operator">≤</a> <a id="34098" href="Presentacion.html#34076" class="Bound">b</a>
         <a id="34109" class="Comment">-----------</a>
         <a id="34130" class="Symbol">→</a> <a id="34132" href="Presentacion.html#34074" class="Bound">a</a> <a id="34134" href="Presentacion.html#34010" class="Function Operator">~</a> <a id="34136" href="Presentacion.html#34076" class="Bound">b</a>

<a id="34139" href="Presentacion.html#34062" class="Function">~-es-≤</a> <a id="34146" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="34151" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="34156" href="Presentacion.html#34156" class="Bound">leq1</a> <a id="34161" class="Symbol">=</a> <a id="34163" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="34168" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="34170" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="34175" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="34180" class="Comment">-- `zero` es tal que testifica lo que se quiere</a>
<a id="34228" href="Presentacion.html#34062" class="Function">~-es-≤</a> <a id="34235" href="Presentacion.html#23851" class="InductiveConstructor">zero</a> <a id="34240" class="Symbol">(</a><a id="34241" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="34245" href="Presentacion.html#34245" class="Bound">b</a><a id="34246" class="Symbol">)</a> <a id="34248" href="Presentacion.html#34248" class="Bound">leq1</a> <a id="34253" class="Symbol">=</a> <a id="34255" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="34259" href="Presentacion.html#34245" class="Bound">b</a> <a id="34261" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="34263" href="Presentacion.html#31512" class="InductiveConstructor">refl</a> <a id="34268" class="Symbol">(</a><a id="34269" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="34273" href="Presentacion.html#34245" class="Bound">b</a><a id="34274" class="Symbol">)</a> <a id="34276" class="Comment">-- `suc b` testifica que `zero + suc b ≡ suc b`</a>
<a id="34324" href="Presentacion.html#34062" class="Function">~-es-≤</a> <a id="34331" class="Symbol">(</a><a id="34332" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="34336" href="Presentacion.html#34336" class="Bound">a</a><a id="34337" class="Symbol">)</a> <a id="34339" class="Symbol">(</a><a id="34340" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="34344" href="Presentacion.html#34344" class="Bound">b</a><a id="34345" class="Symbol">)</a> <a id="34347" href="Presentacion.html#34347" class="Bound">leq1</a> <a id="34352" class="Symbol">=</a> <a id="34354" href="Presentacion.html#34431" class="Function">k</a> <a id="34356" href="Agda.Builtin.Sigma.html#218" class="InductiveConstructor Operator">,</a> <a id="34358" href="Presentacion.html#34553" class="Function">AF2</a>
  <a id="34364" class="Keyword">where</a>
    <a id="34374" href="Presentacion.html#34374" class="Function">HI</a> <a id="34377" class="Symbol">:</a> <a id="34379" href="Presentacion.html#33954" class="Function">∃</a> <a id="34381" href="Presentacion.html#34381" class="Bound">k</a> <a id="34383" href="Presentacion.html#33954" class="Function">∈</a> <a id="34385" href="Presentacion.html#23834" class="Datatype">ℕ</a> <a id="34387" href="Presentacion.html#33954" class="Function">,</a> <a id="34389" class="Symbol">(</a><a id="34390" href="Presentacion.html#34336" class="Bound">a</a> <a id="34392" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="34394" href="Presentacion.html#34381" class="Bound">k</a><a id="34395" class="Symbol">)</a> <a id="34397" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="34399" href="Presentacion.html#34344" class="Bound">b</a>
    <a id="34405" href="Presentacion.html#34374" class="Function">HI</a> <a id="34408" class="Symbol">=</a> <a id="34410" href="Presentacion.html#34062" class="Function">~-es-≤</a> <a id="34417" href="Presentacion.html#34336" class="Bound">a</a> <a id="34419" href="Presentacion.html#34344" class="Bound">b</a> <a id="34421" href="Presentacion.html#34347" class="Bound">leq1</a>

    <a id="34431" href="Presentacion.html#34431" class="Function">k</a> <a id="34433" class="Symbol">:</a> <a id="34435" href="Presentacion.html#23834" class="Datatype">ℕ</a>
    <a id="34441" href="Presentacion.html#34431" class="Function">k</a> <a id="34443" class="Symbol">=</a> <a id="34445" href="Agda.Builtin.Sigma.html#234" class="Field">fst</a> <a id="34449" href="Presentacion.html#34374" class="Function">HI</a>

    <a id="34457" href="Presentacion.html#34457" class="Function">HI&#39;</a> <a id="34461" class="Symbol">:</a> <a id="34463" class="Symbol">(</a><a id="34464" href="Presentacion.html#34336" class="Bound">a</a> <a id="34466" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="34468" href="Presentacion.html#34431" class="Function">k</a><a id="34469" class="Symbol">)</a> <a id="34471" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="34473" href="Presentacion.html#34344" class="Bound">b</a>
    <a id="34479" href="Presentacion.html#34457" class="Function">HI&#39;</a> <a id="34483" class="Symbol">=</a> <a id="34485" href="Agda.Builtin.Sigma.html#246" class="Field">snd</a> <a id="34489" href="Presentacion.html#34374" class="Function">HI</a>

    <a id="34497" href="Presentacion.html#34497" class="Function">AF1</a> <a id="34501" class="Symbol">:</a> <a id="34503" class="Symbol">(</a><a id="34504" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="34508" href="Presentacion.html#34336" class="Bound">a</a> <a id="34510" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="34512" href="Presentacion.html#34431" class="Function">k</a><a id="34513" class="Symbol">)</a> <a id="34515" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="34517" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="34521" class="Symbol">(</a><a id="34522" href="Presentacion.html#34336" class="Bound">a</a> <a id="34524" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="34526" href="Presentacion.html#34431" class="Function">k</a><a id="34527" class="Symbol">)</a>
    <a id="34533" href="Presentacion.html#34497" class="Function">AF1</a> <a id="34537" class="Symbol">=</a> <a id="34539" href="Presentacion.html#33067" class="Function">+-suc</a> <a id="34545" href="Presentacion.html#34431" class="Function">k</a> <a id="34547" href="Presentacion.html#34336" class="Bound">a</a>
    <a id="34553" href="Presentacion.html#34553" class="Function">AF2</a> <a id="34557" class="Symbol">:</a> <a id="34559" class="Symbol">(</a><a id="34560" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="34564" href="Presentacion.html#34336" class="Bound">a</a> <a id="34566" href="Presentacion.html#28194" class="Function Operator">+</a> <a id="34568" href="Presentacion.html#34431" class="Function">k</a><a id="34569" class="Symbol">)</a> <a id="34571" href="Presentacion.html#31474" class="Datatype Operator">≡</a> <a id="34573" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="34577" href="Presentacion.html#34344" class="Bound">b</a>
    <a id="34583" href="Presentacion.html#34553" class="Function">AF2</a> <a id="34587" class="Symbol">=</a> <a id="34589" href="Presentacion.html#32045" class="Function">≡-trans</a> <a id="34597" href="Presentacion.html#34497" class="Function">AF1</a> <a id="34601" class="Symbol">(</a><a id="34602" href="Presentacion.html#32702" class="Function">cong</a> <a id="34607" href="Presentacion.html#23862" class="InductiveConstructor">suc</a> <a id="34611" href="Presentacion.html#34457" class="Function">HI&#39;</a><a id="34614" class="Symbol">)</a>
</pre>
# Esto concluye la presentación.
## ¡Muchas gracias por su atención!

# TODO
> Mencionar a que aplicación de juicios corresponden las combinaciones de teclas en agda
[Agda Docs](https://agda.readthedocs.io/en/v2.5.2/tools/emacs-mode.html)
