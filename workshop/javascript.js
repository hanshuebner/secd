// -*- Java -*-

/* cms support */

function check(button, checkboxname, b) {
  checkboxes = button.form[checkboxname];
  for (i = 0; i < checkboxes.length; i++) {
    checkboxes[i].checked = b;
  }
}

/* profile editor */

function check_password(form) {
    if (form.password.value != form.password_repeat.value) {
	alert('Please enter the same password twice');
	form.password.focus();
	return false;
    } else {
	return true;
    }
}
