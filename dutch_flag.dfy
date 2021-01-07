datatype Color = Red | White | Blue

predicate Below(a: Color, b: Color)
{
    a == Red || b == Blue || a == b
}

method DutchFlag(a: array<Color>)
    modifies a
    ensures forall i,j :: 0 <= i < j < a.Length ==> Below(a[i], a[j])
    ensures multiset(a[..]) == multiset(old(a[..])) 
{
    var r, w, b := 0, 0, a.Length;
    while w < b 
        decreases b - w
        invariant 0 <= r <= w <= b <= a.Length
        invariant forall i :: 0 <= i < r ==> a[i] == Red
        invariant forall i :: r <= i < w ==> a[i] == White
        invariant forall i :: b <= i < a.Length ==> a[i] == Blue
        invariant multiset(a[..]) == multiset(old(a[..])) 
    {
        match a[w]
        case Red =>
            a[r], a[w] := a[w], a[r];
            r, w := r + 1, w + 1;
        case White =>
            w := w + 1;
        case Blue =>
            a[b - 1], a[w] := a[w], a[b-1];
            b := b - 1;
    }
}