import React from "react";
import IconButton from "../components/IconButton/IconButton";

import { BackupTable, TableChart } from "@mui/icons-material";
import InfoIcon from "@mui/icons-material/Info";
import ZoomOutMapIcon from "@mui/icons-material/ZoomOutMap";

export default {
    title: "components/Icon Button",
    component: IconButton,
    argTypes: { onClick: { action: "onClick" } },
};

export const HelpText = {
    args: {
        icon: <InfoIcon />,
        round: true,
    },
};

export const DetailedData = {
    args: {
        icon: <BackupTable />,
        round: false,
    },
};

export const ChangeView = {
    args: {
        icon: <TableChart />,
        round: true,
    },
};
export const MaxView = {
    args: {
        icon: <ZoomOutMapIcon />,
        round: true,
    },
};
