toggleAbstract = s => {
  const negate = v => v === 'inline' ? 'none' : 'inline';
  const id = s + '-abstract';
  const d = negate(document.getElementById(id).style.display);
  document.getElementById(id).style.display = d;
  if (d === 'inline') document.getElementById(s + '-notes').style.display = 'none';
}
toggleNotes = s => {
  const negate = v => v === 'inline' ? 'none' : 'inline';
  const id = s + '-notes';
  const d = negate(document.getElementById(id).style.display);
  document.getElementById(id).style.display = d;
  if (d === 'inline') document.getElementById(s + '-abstract').style.display = 'none';
}