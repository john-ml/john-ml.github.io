toggleAbstract = s => {
  const negate = v => v === 'inline' ? 'none' : 'inline';
  const id = s + '-abstract';
  document.getElementById(id).style.display = negate(document.getElementById(id).style.display);
}