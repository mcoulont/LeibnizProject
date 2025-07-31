
if (
    localStorage.getItem("prover") != "Lean4" ||
    ! leanIsUsed()
) {
    localStorage.setItem("prover", "Rocq");
}

if (rocqIsUsed() && leanIsUsed()) {
    const proversIcons = document.getElementsByClassName("prover-icon");

    for (let i = 0; i < proversIcons.length; i++) {
        proversIcons[i].onclick = switchProver;
        proversIcons[i].style.cursor = "pointer";

        if ("rocq-code" == proversIcons[i].parentElement.className) {
            proversIcons[i].title += "\nClick to switch to Lean4";
        } else {
            proversIcons[i].title += "\nClick to switch to Rocq";
        }
    }

    document.getElementById("rocq-bottom-icon").onclick = switchProver;
    document.getElementById("lean-bottom-icon").onclick = switchProver;
    document.getElementById("rocq-bottom-icon").style.cursor = "pointer";
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
    if (proverIsRocq()) {
        return "Lean4";
    } else {
        return "Rocq";
    }
}

function proverIsRocq() {
    return "Rocq" == getProver();
}

function proverIsLean() {
    return "Lean4" == getProver();
}

function rocqIsUsed() {
    return 0 != document.getElementsByClassName("rocq-code").length;
}

function leanIsUsed() {
    return 0 != document.getElementsByClassName("lean-code").length;
}


function setDisplay(id, display) {
    if (null != document.getElementById(id)) {
        document.getElementById(id).style.display = display;
    }
}

function setDisplayByClassName(className, display) {
    const elements = document.getElementsByClassName(className);

    for (let i = 0; i < elements.length; i++) {
        elements[i].style.display = display;
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
    let rocqUsed = rocqIsUsed();
    let leanUsed = leanIsUsed();

    if (rocqUsed) {
        setDisplay("links-rocq", "inline");

        if (proverIsRocq()) {
            setDisplayByClassName("rocq-code", "grid");
            setDisplay("rocq-bottom-icon", "none");
        } else {
            setDisplayByClassName("rocq-code", "none");
            setDisplay("rocq-bottom-icon", "inline");
        }
    } else {
        setDisplayByClassName("rocq-code", "none");
        setDisplay("links-rocq", "none");
    }

    if (leanUsed) {
        setDisplay("links-lean", "inline");

        if (proverIsLean()) {
            setDisplayByClassName("lean-code", "grid");
            setDisplay("lean-bottom-icon", "none");
        } else {
            setDisplayByClassName("lean-code", "none");
            setDisplay("lean-bottom-icon", "inline");
        }
    } else {
        setDisplayByClassName("lean-code", "none");
        setDisplay("links-lean", "none");
    }

    if (rocqUsed && leanUsed) {
        document.getElementById("prover").innerText = getProver();
        document.getElementById("other-prover").innerText = getOtherProver();

        setDisplay("links-and", "inline");
    } else {
        setDisplay("links-and", "none");
    }
}
