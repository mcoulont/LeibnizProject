
if (localStorage.getItem("prover") != "Lean4") {
    localStorage.setItem("prover", "Coq");
}

if (coqIsUsed() && leanIsUsed()) {
    const proversIcons = document.getElementsByClassName("prover-icon");

    for (let i = 0; i < proversIcons.length; i++) {
        proversIcons[i].onclick = switchProver;
        proversIcons[i].style.cursor = "pointer";

        if ("coq-code" == proversIcons[i].parentElement.id) {
            proversIcons[i].title += "\nClick to switch to Lean4";
        } else {
            proversIcons[i].title += "\nClick to switch to Coq";
        }
    }

    document.getElementById("coq-bottom-icon").onclick = switchProver;
    document.getElementById("lean-bottom-icon").onclick = switchProver;
    document.getElementById("coq-bottom-icon").style.cursor = "pointer";
    document.getElementById("lean-bottom-icon").style.cursor = "pointer";

    document.getElementById("links-provers").style.marginTop = "1em";
} else {
    setDisplay("switch-prover", "none");
}

refreshDisplay();


function getProver() {
    return localStorage.getItem("prover");
}

function getOtherProver() {
    if (proverIsCoq()) {
        return "Lean4";
    } else {
        return "Coq";
    }
}

function proverIsCoq() {
    return "Coq" == getProver();
}

function proverIsLean() {
    return "Lean4" == getProver();
}

function coqIsUsed() {
    return null != document.getElementById("coq-code");
}

function leanIsUsed() {
    return null != document.getElementById("lean-code");
}


function setDisplay(id, display) {
    if (null != document.getElementById(id)) {
        document.getElementById(id).style.display = display;
    }
}


function switchProver() {
    localStorage.setItem(
        "prover",
        getOtherProver()
    );

    refreshDisplay();
}


function refreshDisplay() {
    let coqUsed = coqIsUsed();
    let leanUsed = leanIsUsed();

    if (coqUsed) {
        setDisplay("links-coq", "inline");

        if (proverIsCoq()) {
            setDisplay("coq-code", "grid");
            setDisplay("coq-bottom-icon", "none");
        } else {
            setDisplay("coq-code", "none");
            setDisplay("coq-bottom-icon", "inline");
        }
    } else {
        setDisplay("links-coq", "none");
        setDisplay("coq-code", "none");
    }

    if (leanUsed) {
        setDisplay("links-lean", "inline");

        if (proverIsLean()) {
            setDisplay("lean-code", "grid");
            setDisplay("lean-bottom-icon", "none");
        } else {
            setDisplay("lean-code", "none");
            setDisplay("lean-bottom-icon", "inline");
        }
    } else {
        setDisplay("links-lean", "none");
        setDisplay("lean-code", "none");
    }

    if (coqUsed && leanUsed) {
        document.getElementById("prover").innerText = getProver();
        document.getElementById("other-prover").innerText = getOtherProver();

        setDisplay("links-and", "inline");
    } else {
        setDisplay("links-and", "none");
    }
}
