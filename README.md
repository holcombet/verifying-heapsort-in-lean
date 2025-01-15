# HeapSort

This project aimed to verify the HeapSort algorithm using the Lean theorem prover. The [HeapSort source code](https://github.com/holcombet/verifying-heapsort-in-lean/blob/main/heapSort.hs) was translated from Haskell to Lean, and formally verified [in Lean](https://github.com/holcombet/verifying-heapsort-in-lean/blob/main/HeapSort.lean). 


## Semi-Formal Proof of the Invariant

**Lemma 1:** if x $\in$ (a, L, R) then x = a $\lor$ x $\in$ L $\lor$ x $\in$ R

**Lemma 2:** if x $\in$ t then x $\in$ insert(y, t)

**Proposition inInsert:** if x $\in$ insert(y, t) then x = y or x $\in$ t

Proof.

> Assume: x $\in$ insert(y, t) \
> Show: x = y $\lor$ x $\in$ t 
>
> Case: t = Nil \
> insert(y, Nil) = (y, Nil, Nil) \
> x $\in$ (y, Nil, Nil). \ 
> x = y \
> x = y $\lor$ x $\in$ t
>
>
> Case: t = (a, L, R) \
> IH1: x $\in$ insert(y, L) $\to$ x = y $\lor$ x $\in$ L \
> IH2: x $\in$ insert(y, R) $\to$ x = y $\lor$ x $\in$ R 
>
> y $\le$ a or y $>$ a
>
>> Assume: y $\le$ a \
>> insert(y, t) = (a, insert(y,L), R) \
>> x $\in$ (a, insert(y, L), R) \
>> x = a $\lor$ x $\in$ insert(y, L) $\lor$ x $\in$ R ... Lemma 1 
>>> Assume: x = a \
>>> x $\in$ t \
>>> x = y $\lor$ x $\in$ t
>> 
>>> Assume: x $\in$ insert(y, L) \
>>> x = y $\lor$ x $\in$ L ... IH1 \
>>> x = y $\lor$ x $\in$ t
>>
>>> Assume: x $\in$ R \
>>> x $\in$ insert(y, R) ... Lemma 2 \
>>> x $\in$ y $\lor$ x $\in$ R ... IH2 \
>>> x $\in$ y $\lor$ x $\in$ t
>>
>> x = y $\lor$ x $\in$ t
>>
>> Assume: y $>$ a\
>> insert(y, t) = (a, L, insert(y, R)) \
>> x $\in$ (a, L, insert(y, R)) \
>> x = a $\lor$ x $\in$ L $\lor$ x $\in$ insert(y,R)
>>> Assume: x = a \
>>> x $\in$ t \
>>> x = y $\lor$ x $\in$ t 
>>
>>> Assume: x $\in$ L \
>>> x $\in$ insert(y, L) ... Lemma 2 \
>>> x = y $\lor$ x $\in$ L ... IH1 \
>>> x = y $\lor$ x $\in$ t
>>
>>> Assume: x $\in$ insert(y, R) \
>>> x = y $\lor$ x $\in$ R ... IH2 \
>>> x = y $\lor$ x $\in$ t 
>>
>> x = y $\lor$ x $\in$ t 
>
> x = y $\lor$ x $\in$ t

QED



### Lemma: Invariant

Proof. 

Assume: heap(t) \
Show: heap(insert(x,t))

Case: t = Nil \
insert(x, Nil) = (x, Nil, Nil) \
(x, Nil, Nil) is a heap by our understanding of a singleton.

Case: t = (y, L, R) \
IH1: heap(L) $\to$ heap(insert(x, L)) \
IH2: heap(R) $\to$ heap(insert(x, R))

x $\le$ y or x $>$ y

Assume: x $\le$ y 
> heap(insert(x, (y, L, R))) = heap((y, insert(x, L), R)) \
> heap(insert(x, L)) $\land$ heap(R) $\land$ ($\forall$ (a $\in$ $Z$), a $\in$ insert(x, L) $\to$ a $\le$ y) $\land$ ($\forall$ (b $\in Z$), b $\in$ R $\to$ b $\ge$ y) 
>> heap(insert(x, L)) ... by IH1 
>
>> heap(R) ... by assumption 
>
>> ($\forall$ (a $\in Z$), a $\in$ insert(x, L) $\to$ a $\le$ y) \
>> Assume: a $\in$ insert(x, L) 
>>> x = a $\lor$ a $\in$ L ... Proposition inInsert \
>>> x = a  
>>>> a $\le$ y 
>>>
>>> a $\in$ L 
>>>> a $\le$ y 
>
>> ($\forall$ (b $\in Z$, b $\in$ R $\to$ b $\ge$ y)) ... by assumption
>
>> Assume: x $>$ y
>>>heap(insert(x, (y, L, R))) = heap((y, L, (insert(x, R))))
>>> heap(L) $\land$ heap(insert(x, R)) $\land$ ($\forall$ (a $\in Z$), a $\in$ L $\to$ a $\le$ x) $\land$ ($\forall$ (b $\in Z$), b $\in$ insert(x, R) $\to$ b $\ge$ y)
>>>> heap(L) ... by assumption 
>>>
>>>> heap(insert(x, R)) ... by IH2 
>>>
>>>> ($\forall$ (a $\in Z$), a $\in$ L $\to$ a $\le$ x) ... by assumption 
>>>
>>>> ($\forall$ (b $\in Z$), b $\in$ insert(x, R) $\to$ b $\ge$ y) \
>>>> Assume: b $\in$ insert(x, R) \
>>>> x = b $\lor$ b $\in$ R ... by proposition inInsert \
>>>> x = b 
>>>>> x $>$ y
>>>>>
>>>> b $\in$ R
>>>>>
>>>> b $>$ y 
>
> QED