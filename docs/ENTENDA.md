# Entendendo Soma

> Note: This is an AI-generated translation of the [original English document](UNDERSTAND.md).

Este documento tem como objetivo fornecer uma compreensão abrangente dos fundamentos teóricos por trás de Soma, uma linguagem de programação baseada em combinadores de interação. Exploraremos o contexto histórico das linguagens de programação, os princípios da lógica linear, o conceito de redes de interação e, finalmente, as especificidades dos combinadores de interação.

Então, discutiremos como Soma aproveita esses conceitos para oferecer uma experiência de programação única, focando em suas aplicações práticas e vantagens.

Índice:
1. [Contexto Histórico](#contexto-histórico)
  - 1.1 [Modelos de Computação](#modelos-de-computação)
  - 1.2 [Lógica Linear](#lógica-linear)
  - 1.3 [Redes de Interação](#redes-de-interação)
  - 1.4 [Combinadores de Interação](#combinadores-de-interação)
  - 1.5 [Cálculo de Interação](#cálculo-de-interação)
  - 1.6 [Resumo](#resumo)
2. [Onde o Soma Entra](#onde-o-soma-entra)
  - 2.1 [Uma Linguagem que Você Pode Realmente Usar](#uma-linguagem-que-você-pode-realmente-usar)
  - 2.2 [Sem Coletor de Lixo](#sem-coletor-de-lixo)
  - 2.3 [Avaliação Estrita com Compartilhamento Ótimo](#avaliação-estrita-com-compartilhamento-ótimo)
  - 2.4 [Paralelismo de Graça](#paralelismo-de-graça)
  - 2.5 [Por que Isso Importa para Você](#por-que-isso-importa-para-você)
3. [Agradecimentos](#-agradecimentos)

# Contexto Histórico

## Modelos de Computação

Ao longo da história da ciência da computação, as linguagens de programação giraram em torno de dois modelos de computação:

1. **Máquinas de Turing**: São máquinas abstratas que manipulam símbolos em uma fita de acordo com um conjunto de regras. São usadas para modelar processos algorítmicos e são fundamentais na teoria da computação.

> Exemplos: Python, Java, C++ e muitas outras linguagens de programação imperativas e orientadas a objetos são baseadas no modelo da máquina de Turing. Elas focam em mudança de estado através de instruções e estruturas de controle.

2. **Cálculo Lambda**: Este é um sistema formal para expressar computação baseado em abstração e aplicação de funções. Serve como fundamento teórico para linguagens de programação funcional.

> Exemplos: Haskell, Lisp e Erlang são exemplos de linguagens de programação funcional baseadas nos princípios do cálculo lambda. Elas enfatizam o uso de funções e imutabilidade.

No entanto, há desvantagens significativas em ambos. Linguagens baseadas em máquinas de Turing podem levar a gerenciamento de estado complexo e efeitos colaterais, dificultando o raciocínio sobre programas. Por outro lado, embora linguagens baseadas em cálculo lambda promovam abstrações mais limpas, elas podem ter dificuldades com efeitos colaterais e computações com estado, que são frequentemente necessários em aplicações do mundo real.

Isso acontece porque linguagens de programação funcional são muito inspiradas na correspondência de Curry-Howard, que estabelece uma relação direta entre programas de computador e provas matemáticas. Em Curry-Howard, tipos são proposições e funções são provas. Por exemplo, `id : A -> A` é uma prova de que a partir da proposição A, podemos derivar a proposição A. Essa correspondência encoraja uma visão da programação como construção de provas, levando a um foco em funções puras e imutabilidade.

Mas houve críticas significativas à lógica clássica e intuicionista, que fundamentam grande parte da programação funcional. Isso porque elas assumem que não há gerenciamento de recursos!

Programação funcional é frequentemente evitada porque são percebidas como ineficientes em termos de uso de recursos, particularmente memória e poder de processamento. Isso porque linguagens de programação funcional frequentemente dependem de estruturas de dados imutáveis e recursão, o que pode levar a maior consumo de memória e desempenho mais lento comparado a linguagens imperativas que usam estado mutável e construções iterativas.

Na lógica clássica/intuicionista, suposições podem ser usadas livremente e descartadas após o uso. Isso não reflete cenários do mundo real onde recursos são frequentemente limitados e devem ser gerenciados cuidadosamente. Por exemplo, se você tem um handle de arquivo ou uma conexão de rede, você não pode simplesmente usá-lo uma vez e descartá-lo; você precisa garantir que ele seja propriamente fechado ou liberado após o uso.

## Lógica Linear

A lógica linear, introduzida por Jean-Yves Girard em 1987, aborda esses problemas tratando suposições como recursos que devem ser usados exatamente uma vez. Isso significa que se você tem um recurso, você deve usá-lo em sua computação, e você não pode simplesmente descartá-lo ou duplicá-lo sem permissão explícita.

Isso é o que levou ao desenvolvimento de sistemas de tipos lineares em linguagens de programação como Rust. O modelo de propriedade do Rust é uma implementação prática dos princípios da lógica linear. Em Rust, cada valor tem um único dono, e quando o dono sai do escopo, o valor é automaticamente desalocado. Isso garante que recursos sejam gerenciados de forma eficiente e segura, prevenindo problemas como vazamentos de memória e corrupção de dados.

Como bônus, a lógica linear também tem mecanismos integrados para concorrência e paralelismo. Como recursos devem ser usados exatamente uma vez, isso naturalmente leva a um modelo onde computações podem ser realizadas em paralelo sem o risco de condições de corrida ou corrupção de dados.

> Nota: não tem nada a ver com álgebra linear ou equações lineares!

## Redes de Interação

Depois que a lógica linear foi teorizada, vários pesquisadores perceberam que ela poderia modelar computação funcional com o bônus de gerenciamento de recursos refinado. Isso levou a variantes do cálculo lambda e ao desenvolvimento das Redes de Interação por Yves Lafont em 1990.

A ideia central das Redes de Interação é representar computações como uma rede de nós interconectados, onde cada nó representa uma operação computacional, e as arestas representam o fluxo de dados entre essas operações. A característica chave das Redes de Interação é que elas permitem interações locais entre nós, significando que computações podem ser realizadas em paralelo sem a necessidade de uma estrutura de controle global.

A conexão chave com a lógica linear é que redes de interação podem naturalmente codificar redes de provas da lógica linear (uma representação gráfica de provas em lógica linear). Cada interação na rede corresponde a uma inferência lógica, e a estrutura da rede reflete os princípios de gerenciamento de recursos da lógica linear.

Redes de interação são basicamente:
1. Um conjunto de agentes (nós) com portas
2. Um conjunto de fios conectando as portas
3. Um avaliador que aplica regras de interação a pares de agentes conectados

Se dois agentes estão conectados via suas portas principais, eles podem interagir de acordo com regras predefinidas, transformando a rede.

Pense assim: portas principais representam como um nó é usado por outros nós e mostram o fluxo de computação que depende deste nó. Portas auxiliares, por outro lado, carregam a informação que o nó precisa para existir ou computar, codificando as entradas necessárias para o nó fazer seu trabalho.

```Haskell
let x = 5 in x + 10
```

Aqui, a visualização em redes de interação é:

```
  [let]
  /   \ 
[5]    [+]
       / \
    (x)   [10]
     |
    [5]
```

## Combinadores de Interação

Também desenvolvidos por Yves Lafont em 1997, seu objetivo com os Combinadores de Interação era encontrar o sistema de interação universal mais simples possível. Ele conseguiu isso com apenas três tipos de agentes:

1. **γ (gama):** o construtor. Ele constrói e desconstrói estruturas de dados como pares, listas ou nós de árvore.
2. **δ (delta):** o duplicador. Ele copia dados quando um valor precisa ser usado mais de uma vez.
3. **ε (épsilon):** o apagador. Ele coleta como lixo dados que não são mais necessários.

Esses agentes interagem de acordo com regras simples quando se encontram via suas portas principais:

- **Aniquilação (γ-γ ou δ-δ):** Quando dois agentes do mesmo tipo colidem, eles se cancelam e seus fios auxiliares se conectam diretamente. Pense nisso como um construtor encontrando um destrutor—eles se desfazem mutuamente.

- **Comutação (γ-δ):** Quando um construtor encontra um duplicador, eles "passam através" um do outro. O duplicador clona o construtor, e o construtor divide o duplicador. É assim que a cópia se propaga através de uma estrutura de dados.

- **Apagamento (ε-qualquer coisa):** Quando um apagador encontra qualquer agente, ele destrói esse agente e gera apagadores para cada uma de suas portas auxiliares. A coleta de lixo cascateia através da estrutura.

O que torna este sistema notável é sua universalidade: esses três agentes e suas regras de interação são suficientes para codificar qualquer computação. Qualquer máquina de Turing, qualquer termo do cálculo lambda, qualquer algoritmo pode ser representado e executado usando apenas γ, δ e ε.

A beleza está na localidade e paralelismo. Cada interação envolve apenas dois agentes e suas conexões imediatas. Isso significa nenhum estado global, nenhuma memória compartilhada, nenhuma sincronização necessária. Quaisquer duas interações independentes podem acontecer simultaneamente. Isso torna os combinadores de interação uma fundação ideal para computação massivamente paralela.

Para citar as palavras de Victor Taelin (Soma só é possível por causa de sua pesquisa e trabalho público que me fez aprender tudo isso):

> "Curiosamente, todo aspecto que é considerado bom em outros modelos de computação está presente nos Combinadores de Interação, enquanto aspectos negativos estão quase inteiramente ausentes. Além disso, tanto o Cálculo Lambda quanto a Máquina de Turing podem ser eficientemente emulados pelos Combinadores de Interação, enquanto o oposto não é verdade. Isso sugere que, embora os 3 sistemas sejam equivalentes em termos de computabilidade, os Combinadores de Interação são mais capazes em termos de computação. Sob certo ponto de vista, poder-se-ia argumentar que tanto a Máquina de Turing quanto o Cálculo Lambda são leves distorções deste modelo fundamental, causadas pela criatividade humana, devido às nossas intuições históricas sobre máquinas e matemática. Talvez máquinas e substituições não sejam tão fundamentais quanto pensamos, e alguma civilização alienígena tenha desenvolvido todas as suas teorias matemáticas e computadores baseados em aniquilação e comutação, sem referências ao Cálculo Lambda ou à Máquina de Turing."

Esta é minha citação favorita sobre Combinadores de Interação porque resume perfeitamente por que acredito que eles são o futuro da computação.

## Cálculo de Interação

Enquanto combinadores de interação são universais e elegantes, eles são de baixo nível—como escrever assembly para grafos de computação. Programar diretamente com γ, δ e ε é tedioso. O que precisamos é uma linguagem de alto nível que compile para combinadores de interação.

É aqui que entra o Cálculo de Interação (CI), também desenvolvido por Victor Taelin. É essencialmente cálculo lambda redesenhado desde o início para mapear naturalmente em redes de interação. O resultado é um cálculo que parece familiar para programadores funcionais mas tem semântica radicalmente diferente.

Três mudanças chave distinguem o CI do cálculo lambda tradicional:

1. **Variáveis afins:** Cada variável pode ser usada no máximo uma vez. Isso reflete diretamente a fundação da lógica linear—cada valor é um recurso que deve ser consumido exatamente uma vez (ou explicitamente descartado).

2. **Escopo global:** Variáveis não são vinculadas ao seu escopo léxico. Elas podem aparecer em qualquer lugar do programa. Isso soa caótico, mas é na verdade o que permite o compartilhamento ótimo.

3. **Superposições e duplicações:** Quando você precisa usar um valor mais de uma vez, você não apenas o copia. Em vez disso, você cria uma *superposição*—um valor que existe em múltiplos "ramos" simultaneamente. Uma *duplicação* então colapsa esses ramos quando necessário.

O mecanismo de superposição/duplicação é o que torna o CI especial. No cálculo lambda normal, se você escreve `let x = caro() in x + x`, o termo `caro()` pode ser computado duas vezes. Avaliadores ótimos resolvem isso através de contabilidade complexa. No CI, a solução é incorporada na própria linguagem: `caro()` se torna uma superposição que é compartilhada entre ambos os usos, e a duplicação acontece preguiçosamente (ou no caso do Soma, avidamente) apenas quando os valores realmente precisam divergir.

Isso dá ao CI algo notável: *avaliação ótima* por construção. A representação em rede de interação automaticamente compartilha computação da maneira mais eficiente possível, evitando trabalho redundante que aflige linguagens funcionais tradicionais.

A contrapartida é que o CI não pode expressar certos termos do cálculo lambda—notavelmente auto-aplicação como `λx.(x x)`, já que isso exigiria usar `x` duas vezes. Mas na prática, essa restrição elimina os padrões que causam explosão exponencial na avaliação, transformando-os na computação compartilhada eficiente em que redes de interação se destacam.

## Resumo

- Linguagens de programação tradicionais são baseadas em máquinas de Turing (imperativo) ou cálculo lambda (funcional), ambas com limitações em gerenciamento de recursos e paralelismo.
- Lógica linear trata suposições como recursos que devem ser usados exatamente uma vez, levando a melhor gerenciamento de recursos
- Redes de interação representam computações como redes de nós que interagem localmente, permitindo paralelismo e uso eficiente de recursos.
- Combinadores de interação são um sistema universal mínimo usando apenas três tipos de agentes (construtor, duplicador, apagador) que podem representar qualquer computação através de interações locais.
- Cálculo de interação é uma linguagem de alto nível que mapeia em redes de interação, usando variáveis afins, escopo global e superposições para alcançar avaliação ótima por construção.

# Onde o Soma Entra

Tudo acima: lógica linear, redes de interação, combinadores de interação, cálculo de interação—é teoria bonita. Mas teoria não entrega produtos, você não pode dizer para uma empresa "só reescreva sua base de código em combinadores de interação, confia em mim". A lacuna entre elegância teórica e programação prática manteve essas ideias confinadas a artigos acadêmicos por décadas.

Soma preenche essa lacuna.

## Uma Linguagem que Você Pode Realmente Usar

Soma é uma linguagem puramente funcional, estaticamente tipada, com inferência de tipos Hindley-Milner. Se você usou Haskell, OCaml, ou até TypeScript com configurações estritas, você vai se sentir em casa. Você escreve código funcional normal: pattern matching, funções de ordem superior, tipos de dados algébricos—e o compilador cuida de todo o resto.

O insight chave é que *você nunca vê as redes de interação*. Você não escreve nós DUP ou pensa sobre superposições. O compilador analisa seu código, infere onde valores precisam ser duplicados ou apagados, e gera a representação em rede de interação ótima automaticamente. É a diferença entre escrever assembly e escrever Python. Exceto que aqui, você obtém a expressividade do Python com o desempenho do assembly.

## Sem Coletor de Lixo

Esta é a característica principal do Soma, e merece ênfase: **Soma não tem coletor de lixo**. Também não requer gerenciamento manual de memória ou lutar constantemente contra um borrow checker.

A maioria das linguagens funcionais paga uma taxa pesada em tempo de execução. Haskell tem um GC geracional sofisticado que pode pausar seu programa imprevisivelmente. O GC do OCaml é rápido mas ainda introduz picos de latência. Até Rust, que evita GC, faz você lutar com lifetimes e regras de propriedade.

Soma segue um caminho diferente. Depois que o compilador lineariza seu código, cada valor tem exatamente um dono e é usado exatamente uma vez. Quando um valor é consumido, ele é liberado imediatamente. Não "eventualmente" por uma thread em segundo plano, não "quando o GC decidir", mas *naquele momento*. Gerenciamento de memória é tão previsível quanto uma chamada `free()` em C, mas você nunca escreve isso você mesmo.

Isso importa para sistemas de tempo real, jogos, sistemas de trading e qualquer lugar onde pausas imprevisíveis são inaceitáveis. Mas também importa para aplicações regulares: sem ajuste de GC, sem inchaço de memória, sem sessões de debugging de "por que meu programa está lento de repente?".

## Avaliação Estrita com Compartilhamento Ótimo

Aqui é onde Soma diverge de outras implementações de redes de interação como HVM (também da HOC de Victor Taelin).

HVM usa avaliação preguiçosa. Isso é teoricamente elegante já que maximiza compartilhamento e alcança redução ótima estilo Lamping. Mas preguiça introduz imprevisibilidade e overhead. Uma expressão aparentemente inocente pode construir um thunk massivo que explode quando finalmente avaliado. Além disso, se um thunk captura muito contexto, pode inchar o uso de memória. Vazamentos de espaço são notoriamente difíceis de debugar.

> Preguiça significa que expressões não são avaliadas até que seus resultados sejam necessários. Então para o código `print(5 + 5)`, em vez de se tornar `print(10)` imediatamente, cria um "thunk" representando a expressão não avaliada `5 + 5`. Apenas quando `print` tenta usar esse valor é que a adição é realmente computada.

Soma usa avaliação estrita (call-by-value). Isso significa que, quando você chama uma função, seu argumento é avaliado primeiro. O que você vê é o que você computa. Isso torna o desempenho previsível e o raciocínio sobre seu código direto.

Mas como a pesquisa da HOC mostra, avaliação teórica ótima estilo Lamping requer preguiça. Então você pode pensar: CBV não é a escolha errada aqui? Bem, meu objetivo desde o início era fazer uma linguagem CBV porque não gosto da preguiça do Haskell. Então pensei "por que não tentar duplicações ansiosas". E elas funcionam e removem as desvantagens da preguiça que não gosto: imprevisibilidade e overhead, sacrificando otimalidade teórica.

O compilador ainda usa redes de interação internamente, ainda insere nós DUP para computação compartilhada, ainda evita trabalho redundante. Você obtém os *benefícios* da redução ótima (sem recomputação de subexpressões compartilhadas) sem os *custos* da preguiça (ordem de avaliação imprevisível, vazamentos de espaço).

É um meio-termo pragmático: semântica previsível para o programador, execução ótima por baixo dos panos.

## Paralelismo de Graça

Lembra como redes de interação permitem que reduções independentes aconteçam simultaneamente? Se não, isso é o que redes de interação trazem para você: paralelismo gratuito. Como não há efeitos colaterais e nenhum estado compartilhado, quaisquer duas partes da sua computação que não dependem uma da outra podem ser avaliadas em paralelo.

A linguagem tem três modos:
1. **standard:** padrão, runtime previsível (sem preguiça ou paralelismo implícito)
2. **graph:** tudo que pode ser paralelizado, será paralelizado sem nenhum código extra da sua parte
3. **hybrid:** mesmo runtime do modo standard mas com paralelismo fork-join para computações pesadas

No modo graph, o compilador gera código que roda em um runtime paralelo com work-stealing. Partes independentes da sua computação (ramos de uma árvore recursiva, elementos de uma operação map, etc.) são automaticamente distribuídas entre núcleos de CPU. Sem threads para gerenciar, sem locks para debugar, sem condições de corrida para temer.

Em um benchmark simples de fibonacci, Soma alcança **speedup de 8.77x com 4 workers**—isso é escalonamento super-linear, melhor que o máximo teórico, porque a carga de trabalho distribuída cabe melhor nos caches por núcleo. E você não escreveu uma única linha de código paralelo.

Isso é simplesmente a consequência natural de construir sobre redes de interação. Quando seu modelo de computação é inerentemente local e livre de interferência, paralelismo se torna um bônus gratuito em vez de um problema difícil.

## Por que Isso Importa para Você

Se você é um estudante de ciência da computação lendo isso, você pode estar se perguntando: por que eu deveria me importar com mais uma linguagem de programação?

Por mais de 80 anos, construímos linguagens de programação em dois modelos: máquinas de Turing (programação imperativa) e cálculo lambda (programação funcional). Ambos têm falhas profundas. Código imperativo é difícil de raciocinar e lento de programar (senão todo mundo estaria usando ASM e ninguém usaria Go). Código funcional é percebido como lento e guloso por memória.

Redes de interação oferecem um terceiro caminho que é matematicamente mais limpo que ambos, inerentemente paralelo, e eficiente em memória por construção. Mas até agora, isso estava trancado em artigos que apenas estudantes de doutorado leem.

Soma é uma tentativa de tornar essas ideias acessíveis e, em última análise, de provar que você pode ter a expressividade da programação funcional, o desempenho da programação de sistemas, e paralelismo automático, tudo em uma linguagem, sem sacrificar usabilidade. Como grande fã tanto de programação funcional quanto de programação de sistemas, isso é simplesmente uma tentativa de criar minha linguagem dos sonhos.

Minha principal razão para escrever este documento é convidar pessoas que se importarão com este projeto tanto quanto eu. Que serão entusiasmadas em construir um novo tipo de linguagem de programação do zero, baseada em fundamentos teóricos sólidos, e ter uma linguagem de programação para chamar de sua.

O futuro da computação pode não ser máquinas de Turing ou cálculo lambda. Pode ser aniquilação e comutação. E você pode ajudar a construí-lo!

# Agradecimentos

Agradecimentos especiais à **HigherOrderCo** (HOC) e **Victor Taelin** por sua pesquisa e desenvolvimento pioneiros em Redes de Interação e Cálculo de Interação. Seu trabalho em avaliação ótima, o runtime HVM, e os fundamentos teóricos da computação baseada em interação foi instrumental no desenvolvimento do Circuit IR do Soma (a parte do compilador que converte código para cálculo de interação) e sistema de runtime.
