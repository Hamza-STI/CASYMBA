# CASymba

A CAS engine for the TI-84 Plus CE / TI-83 Premium CE calculators.

Source code available at https://github.com/Hamza-STI/CASYMBA/

### License
<a rel="license" href="https://creativecommons.org/licenses/by-nc-sa/4.0/">Creative Commons Attribution-NonCommercial-ShareAlike 4.0<br>
<img alt="Creative Commons License" style="border-width:0" src="https://i.creativecommons.org/l/by-nc-sa/4.0/88x31.png" /></a>




# Presentation :

CASymba est un petit programme de calcul formel destiné aux calculatrices TI-83 Premium CE et TI-84 Plus CE.
Il permet de faire : 
1. de la simplification symbolique
2. calcul de dérivée
3. calcul de dérivée n-ième
4. calcul de dérivée partielle à 2 variables
5. certaines primitives (incomplet)
6. équation de la tangente en un point
7. développement limité / Taylor (***uniquement ce que j'ai vu en étude***)
8. résolution d'équation différentielle d'ordre 1 (avec ou sans conditions - ***uniquement ce que j'ai vu en étude***)
9. résolution d'équation différentielle d'ordre 2 coefficient costant (avec ou sans conditions - ***uniquement ce que j'ai vu en étude***)
10. reste d'une division euclidienne de 2 polynômes
11. pgcd d'une division euclidienne de 2 polynômes
12. quotient d'une division euclidienne de 2 polynômes
13. simplification d'une division de 2 polynômes
14. développement d'expression
15. décomposer en facteur premier (un entier)




# Prérequis

OS 5.3 ou supérieure. si la version est 5.5 ou supérieure, il faut activer l'assembleur avec [Artifice](https://tiplanet.org/forum/archives_voir.php?id=2641766) + [ASMHook](https://tiplanet.org/forum/archives_voir.php?id=2643391).

Il faut transférer le programme en mémoire Archive 

Il faut les [bibliothèques C CE](https://github.com/CE-Programming/libraries/releases/tag/v10.2)




# Guide

Saisissez l'expression sous forme de chaîne de caractères, c'est-à-dire commencer la ligne par un guillemet, exemple : `"X+X+X"`
ensuite exécuter le programme CASYMBA `prgmCASYMBA`



## Calcul de dérivées 

utilisez la fonction `nDeriv(` ***calculatrice en anglais*** ou `nbreDérivé(` ***calculatrice en Français*** accessible dans la touche `math`.

La fonction prend 3 arguments : `nDeriv(EXPRESSION,VARIABLE,VARIABLE)` ou `nDeriv(EXPRESSION,VARIABLE1,VARIABLE2)` ou `nDeriv(EXPRESSION,VARIABLE,ENTIER_POSITIF)`

### Derivée <img src="https://i.imgur.com/VZp2Tg8.png" align="right"> 

pour calculer la dérivée de `x*sin(2*x)` : 

il faut saisir :

```
"nDeriv(X*sin(2*X),X,X)"
prgmCASYMBA
```

### Dérivée n-ième <img src="https://i.imgur.com/7zlKCTm.png" align="left">

pour calculer la dérivée seconde de `x*sin(2*x)` : 

saisir : 

```
"nDeriv(X*sin(2*X),X,2)"
prgmCASYMBA
```

### Dérivée partielle à 2 variables <img src="https://i.imgur.com/NpmRtW0.png" align="right">

pour calculer la dérivée partielle de `y*sin(2*x)` : 

saisir :

```
"nDeriv(Y*sin(2*X),X,Y)"
prgmCASYMBA
```


## calcul de primitive (***certaines primitives***) <img src="https://i.imgur.com/dClTOJc.png" align="right">

***c'est un trop gros programme qui demande de la patiencce et de la connaissance, je n'ai pas encore les moyens de créer quelque chose de complet pour ces modèles***

utilisez la fonction `fnInt(` ***calculatrice en anglais*** ou `intégrFonct(` ***calculatrice en Français*** accessible dans la touche `math`

La fonction prend 4 arguments  : `fnInt(EXPRESSION,VARIABLE,VARIABLE,VARIABLE)`

pour calculer la primitive de `x*exp(x)` : 

saisir : 

```
"fnInt(X*e^(X),X,X,X)"
prgmCASYMBA
```

## Tangente en un point <img src="https://i.imgur.com/xiVhNgc.png" align="right">

utilisez la fonction `Tangent(` ***calculatrice en anglais*** ou `Tangente(` ***calculatrice en Français***

La fonction prend 3 arguments : `Tangent(EXPRESSION,VARIABLE,POINT)`

pour calculer la tangente de `ln(x)` au point 1 : 

saisir :

```
"Tangent(ln(X),X,1)"
prgmCASYMBA
```


## Développment limité / Taylor <img src="https://i.imgur.com/nBTwGN6.png" align="right">

***(il n'y a pas de fonction se rapprochant niveau nom)***

utilisez la fonction `det(` ***calculatrice en anglais*** ou `dét(` ***calculatrice en Français*** 

La fonction prend 4 arguments : `det(EXPRESSION,VARIABLE,ORDRE,POINT)`

pour calculer le dévéloppement limité de `sin(x)` d'ordre 3 au point 0

saisir :

```
"det(sin(X),X,3,0)"
prgmCASYMBA
```


## équation différentielle 

La résolution d'équation différentielle linéaire d'ordre 1 et 2.

utilisez la fonction `solve(` ***calculatrice en anglais*** ou `résoudre(` ***calculatrice en Français***

La fonction prend 3 arguments : `solve(EXPRESSION,VARIABLE,VARIABLE1)`

**remarques : les équations doivent être sous la forme suivante AY'+BY=f(X) ou AY''+BY'+CY=f(X)**

<img src="https://i.imgur.com/M0v07uv.png" align="left">

pour résoudre l'équation différentielle d'ordre 2 de `Y''+2Y'+Y=2*e^(-X)` sans les conditions : 

saisir :

```
"solve(Y''+2Y'+Y=2*e^(-X),X,Y)"
prgmCASYMBA
```
**remarque : il est possible de faire `Y''+2Y'+Y=0` puis `Y''+2Y'+Y=2*e^(-X)`**

pour résoudre l'équation différentielle d'ordre 2 de `Y''+2Y'+Y=2*e^(-X)` avec les conditions suivantes  : 

`f(0) = -1` et `f'(0) = 1` <img src="https://i.imgur.com/ynDPIK7.png" align="right">

saisir :

```
"solve(Y''+2Y'+Y=2*e^(-X) and Y(0)=-1 and Y'(0)=1,X,Y)"
prgmCASYMBA
```

pour résoudre l'équation différentielle d'ordre 1 de `Y'+2Y=2*e^(-2X)` sans condition : ***(pas d'image d'illustration)***

saisir :

```
"solve(Y'+2Y=2*e^(-2X),X,Y)"
prgmCASYMBA
```

<img src="https://i.imgur.com/I7RHeL8.png" align="right">

pour résoudre l'équation différentielle d'ordre 1 de `Y'+2Y=2*e^(-2X)` sans condition : 

saisir :

```
"solve(Y'+2Y=2*e^(-2X) and Y(0)=1,X,Y)"
prgmCASYMBA
```

## Polynômes

quelques fonctions pour la division de 2 polynômes

pour l'exemple par fonction : poly1 = `X^3-6X^2+11X-6` et poly2 = `X^2-6X+8`

### reste de 2 polynômes <img src="https://i.imgur.com/HuFX6JR.png" align="right">

utilisez la fonction `remainder(` ***calculatrice en anglais*** ou `reste(` ***calculatrice en Français***

La fonction prend 3 arguments : `remainder(POLY1,POLY2,VARIABLE)`

pour calculer le reste d'une division euclidienne de 2 polynômes poly1 et poly2 : 

saisir : 

```
"remainder(X^3-6X^2+11X-6,X^2-6X+8,X)"
prgmCASYMBA
```

### PGCD de 2 polynômes <img src="https://i.imgur.com/IW6qkV1.png" align="right">

utilisez la fonction `gcd(` ***calculatrice en anglais*** ou `pgcd(` ***calculatrice en Français***

La fonction prend 3 arguments : `gcd(POLY1,POLY2,VARIABLE)`

pour calculer le pgcd d'une division euclidienne de 2 polynômes poly1 et poly2 : 

saisir : 

```
"gcd(X^3-6X^2+11X-6,X^2-6X+8,X)"
prgmCASYMBA
```

### Quotient de 2 polynômes <img src="https://i.imgur.com/uHbSZvr.png" align="right">

utilisez la fonction `int(` ***calculatrice en anglais*** ou `ent(` ***calculatrice en Français***

La fonction prend 3 arguments : `int(POLY1,POLY2,VARIABLE)`

pour calculer le quotient d'une division euclidienne de 2 polynômes poly1 et poly2 : 

saisir : 

```
"int(X^3-6X^2+11X-6,X^2-6X+8,X)"
prgmCASYMBA
```

### simplification d'une division de 2 polynômes <img src="https://i.imgur.com/Y8suYn5.png" align="right">

utilisez la fonction `expr(`

La fonction prend 3 arguments : `expr(POLY1,POLY2,VARIABLE)`


pour simplifier la division des polynômes poly1 et poly2 : 

saisir : 

```
"expr(X^3-6X^2+11X-6,X^2-6X+8,X)"
prgmCASYMBA
```


## Développement <img src="https://i.imgur.com/h0Us6sQ.png" align="right">

utilisez la fonction `stdDev(` ***calculatrice en anglais*** ou `écart-type(` ***calculatrice en Français***

***(navré pour le choix de la fonction, std fait penser à standard et Dev développement mais en français ça ne fait penser à rien)***

```
"stdDev((A+B)^2)"
prgmCASYMBA
```

## Décomposer un nombre en facteur premier <img src=https://i.imgur.com/oKKuTeK.png align="right">

utilisez la fonction `identity(` ***calculatrice en anglais*** ou `unité(` ***calculatrice en Français***

La fonction prend en argument un nombre entier (idéalement positif)

```
"identity(45)"
prgmCASYMBA
```
