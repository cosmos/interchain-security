Set (h,hash)  21 A
...
Set (h,hash)  22 B

update client  consumer
query vals at height  21
H.vals A
H.next A
H.trustedVals A
H.trustedH 20
C.want A
C.receive A

beginBlock  provider
Set (h,hash)  22 B
endblock  provider
Set (h,hash)  23 A

update client  consumer
query vals at height  22
H.vals A
H.next B
H.trustedVals B
H.trustedH 21
C.want A
C.receive B
