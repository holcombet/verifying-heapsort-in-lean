# HeapSort

This project aimed to verify the HeapSort algorithm using the Lean theorem prover. The [HeapSort source code](https://github.com/holcombet/verifying-heapsort-in-lean/blob/main/heapSort.hs) was translated from Haskell to Lean, and formally verified [in Lean](https://github.com/holcombet/verifying-heapsort-in-lean/blob/main/HeapSort.lean). 

## Semi-Formal Proof of the Invariant

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