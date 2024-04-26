import Button from "../components/Button/Button";

export default {
    title: "Components/Button",
    component: Button,
    argTypes: { onClick: { action: "onClick" } },
};

export const Red = {
    args: {
        label: "Press me",
        backgroundColor: "#e5526d",
        color: "#333",
        size: "md",
    },
};
export const Blue = {
    args: {
        label: "Press me",
        backgroundColor: "rgb(66, 107, 186)",
        color: "#fafafa",
        size: "md",
    },
};

export const Large = {
    args: {
        label: "Press me",
        backgroundColor: "#2ba5dc",
        color: "#fafafa",
        size: "lg",
    },
};

export const Small = {
    args: {
        label: "Press me",
        backgroundColor: "#2ba5dc",
        color: "#fafafa",
        size: "sm",
    },
};
