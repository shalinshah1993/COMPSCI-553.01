fun sumList l = 
	if l = [] then 0
	else hd(l) + sumList(tl(l))

;
