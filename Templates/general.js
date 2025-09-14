
// Initialization

const chooseDisplayTable = document.getElementById("choose-table");
const chooseDisplayIndex = document.getElementById("choose-index");

const buttonShowMath = document.getElementById("switch-visibility-math");
const buttonShowCode = document.getElementById("switch-visibility-code");

if (currentPageIsHomepage()) {
    var tableDisplayed = true;

    chooseDisplayTable.onclick = displayTable;
    chooseDisplayIndex.onclick = displayIndex;
} else {
    if (
        ! leanIsUsed() ||
        localStorage.getItem("prover") != "Lean4"
    ) {
        localStorage.setItem("prover", "Rocq");
    }

    if (localStorage.getItem("showMath") != "false") {
        localStorage.setItem("showMath", "true");
    }

    if (
        // '#' comes from a link to a Rocq object
        window.location.href.includes('#') ||
        localStorage.getItem("showCode") != "false"
    ) {
        localStorage.setItem("showCode", "true");
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

    if (null != buttonShowMath) {
        buttonShowMath.onclick = switchShowMath;
        buttonShowCode.onclick = switchShowCode;
    }
}

refreshDisplay();


// Getters

function currentPageIsHomepage() {
    return null != chooseDisplayTable;
}

function getProver() {
    return localStorage.getItem("prover");
}

function mathIsShown() {
    return "true" == localStorage.getItem("showMath");
}

function codeIsShown() {
    return "true" == localStorage.getItem("showCode");
}

function proverIsRocq() {
    return "Rocq" == getProver();
}

function proverIsLean() {
    return "Lean4" == getProver();
}

function getOtherProver() {
    if (proverIsRocq()) {
        return "Lean4";
    } else {
        return "Rocq";
    }
}

function rocqIsUsed() {
    return 0 != document.getElementsByClassName("rocq-code").length;
}

function leanIsUsed() {
    return 0 != document.getElementsByClassName("lean-code").length;
}


// Events

function switchProver() {
    localStorage.setItem(
        "prover",
        getOtherProver()
    );

    refreshDisplay();
}

function switchShowMath() {
    localStorage.setItem(
        "showMath",
        (localStorage.getItem("showMath") == "true") ? "false" : "true"
    );

    refreshDisplay();
}

function switchShowCode() {
    localStorage.setItem(
        "showCode",
        (localStorage.getItem("showCode") == "true") ? "false" : "true"
    );

    refreshDisplay();
}

function displayTable() {
    tableDisplayed = true

    refreshDisplay();
}

function displayIndex() {
    tableDisplayed = false

    refreshDisplay();
}


// Setters used in refreshDisplay

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


// Variables/display synchronization

function refreshDisplay() {
    if (currentPageIsHomepage()) {
        if (tableDisplayed) {
            chooseDisplayTable.style.borderTop = "5px solid #B2F613"
            chooseDisplayIndex.style.borderTop = "5px solid #0C151C"
            setDisplay("table-contents", "inline");
            setDisplay("rocq-index", "none");
        } else {
            chooseDisplayTable.style.borderTop = "5px solid #0C151C"
            chooseDisplayIndex.style.borderTop = "5px solid #B2F613"
            setDisplay("table-contents", "none");
            setDisplay("rocq-index", "inline");
        }
    } else {
        if (codeIsShown()) {
            buttonShowCode.textContent = "Hide the code";
        } else {
            buttonShowCode.textContent = "Display the code";
        }

        if (mathIsShown()) {
            buttonShowMath.textContent = "Hide the math";
            setDisplayByClassName("math-block", "block");
        } else {
            buttonShowMath.textContent = "Display the math";
            setDisplayByClassName("math-block", "none");
        }

        let rocqUsed = rocqIsUsed();
        let leanUsed = leanIsUsed();

        if (rocqUsed) {
            setDisplay("links-rocq", "inline");

            if (proverIsRocq() && codeIsShown()) {
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

            if (proverIsLean() && codeIsShown()) {
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
}
